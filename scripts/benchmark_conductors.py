#!/usr/bin/env python3
"""Build and audit saved Lean certificates in increasing conductor order.
Only orchestration and external-reference comparison live here; numerical and
arithmetic computation, finite checking, and analytic proofs remain in Lean.
"""

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

JsonObject = dict[str, Any]

if __package__:
    from .conductor_status import write_summary
    from .conductor_validation import binding_source
else:
    from conductor_status import write_summary
    from conductor_validation import binding_source

ROOT = Path(__file__).resolve().parents[1]
SESSION_START = time.monotonic()
SESSION_UTC = datetime.now(UTC).isoformat()
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
MODULARITY = "VerifiedLcalc.Assumptions.ellipticModularity"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path: Path, value: JsonObject) -> None:
    if path.name == "report.json":
        value["session_elapsed_seconds"] = round(time.monotonic() - SESSION_START, 6)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)
    if path.name == "report.json":
        write_summary(path, value)


def run(cmd: list[str], log: Path, timeout: int) -> float:
    start = time.monotonic()
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w") as output:
        proc = subprocess.Popen(
            cmd,
            cwd=ROOT,
            stdout=output,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            code = proc.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
            raise
    elapsed = time.monotonic() - start
    if code != 0:
        raise RuntimeError(f"{cmd!r} exited {code}; see {log}")
    return round(elapsed, 6)


def fixture(path: Path) -> list[JsonObject]:
    rows = json.loads(path.read_text())["inputs"]
    seen = set()
    for r in rows:
        label, N, a = r["label"], r["conductor"], r["ainvs"]
        if not re.fullmatch(r"[1-9][0-9]*\.[a-z]+[1-9][0-9]*", label) or label in seen:
            raise ValueError("Invalid or duplicate input label")
        seen.add(label)
        if (
            type(N) is not int
            or N <= 0
            or int(label.split(".")[0]) != N
            or len(a) != 5
            or any(type(x) is not int for x in a)
        ):
            raise ValueError(f"Malformed input: {label}")
    if not rows:
        raise ValueError("Empty input fixture")
    return rows


def engine_identity() -> JsonObject:
    paths = [
        ROOT / "ConductorMain.lean",
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
    ]
    paths += sorted(
        p
        for p in (ROOT / "VerifiedLcalc").rglob("*.lean")
        if "Certificates" not in p.parts and not p.name.startswith("Generated")
    )
    sources = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT.parent / "mathlib4",
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    data = dict(sources=sources, mathlib_revision=revision, lean_version=version)
    data["sha256"] = hashlib.sha256(
        json.dumps(data, sort_keys=True).encode()
    ).hexdigest()
    return data


def audit_messages(text: str, required: list[str]) -> dict[str, list[str]]:
    found = {}
    for name, body in re.findall(
        r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S
    ):
        found[name] = {x.strip() for x in body.split(",") if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
        found[name] = set()
    results = {}
    for name in required:
        if name not in found:
            raise ValueError(f"Missing component axiom audit: {name}")
        allowed = STANDARD | (
            {MODULARITY}
            if name.endswith((".analytic_rank", ".rank_lower_bound"))
            else set()
        )
        if not found[name] <= allowed:
            raise ValueError(f"Unapproved axiom in {name}: {found[name] - allowed}")
        results[name] = sorted(found[name])
    return results


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--inputs", type=Path, default=ROOT / "data/lmfdb/sql-10000/inputs.json"
    )
    p.add_argument("--references", type=Path)
    p.add_argument(
        "--provenance",
        type=Path,
        help="Optional SQL snapshot metadata; hashes and count are checked",
    )
    p.add_argument("--output", type=Path, default=ROOT / "output/conductors")
    p.add_argument(
        "--conductors", help="Optional comma-separated conductor subset (smoke tests)"
    )
    p.add_argument(
        "--timeout",
        type=int,
        default=3600,
        help="Per-process wall limit; failures are recorded and stop the run",
    )
    p.add_argument("--skip-warm", action="store_true")
    p.add_argument(
        "--resume",
        action="store_true",
        help="Revalidate completed conductors and preserve their original timings",
    )
    args = p.parse_args()
    os.chdir(ROOT)
    os.environ.setdefault("LEAN_NUM_THREADS", "2")
    rows = fixture(args.inputs)
    refs = {}
    if args.references:
        rr = json.loads(args.references.read_text())["references"]
        if len({r["label"] for r in rr}) != len(rr):
            raise ValueError("Duplicate references")
        refs = {r["label"]: r["analytic_rank"] for r in rr}
        if set(refs) != {r["label"] for r in rows}:
            raise ValueError("Reference/input label sets differ")
        if any(v is not None and (type(v) is not int or v < 0) for v in refs.values()):
            raise ValueError("Invalid reference rank")
    provenance = None
    if args.provenance:
        provenance = json.loads(args.provenance.read_text())
        if provenance["inputs_sha256"] != sha(args.inputs) or provenance[
            "count"
        ] != len(rows):
            raise ValueError("SQL provenance/input mismatch")
        if args.references and provenance["references_sha256"] != sha(args.references):
            raise ValueError("SQL provenance/reference mismatch")
        if provenance["raw_sha256"] != sha(args.provenance.parent / "raw.json"):
            raise ValueError("SQL raw capture hash mismatch")
    selected = sorted({r["conductor"] for r in rows})
    if args.conductors:
        wanted = {int(n) for n in args.conductors.split(",")}
        if not wanted <= set(selected):
            raise ValueError("Requested conductor absent from input")
        selected = [n for n in selected if n in wanted]
    identity = engine_identity()
    prefix = (
        "VerifiedLcalc.Certificates.ConductorRuns.S"
        + sha(args.inputs)[:16]
        + "_E"
        + identity["sha256"][:16]
    )
    directory = args.output / (
        prefix.split(".")[-1]
        + "_R"
        + (sha(args.references)[:16] if args.references else "none")
    )
    directory.mkdir(parents=True, exist_ok=True)
    source_hashes = identity["sources"].copy()
    global_audits = sorted(ROOT.glob("Audit*.lean"))
    imports = []
    bodies = []
    for f in global_audits:
        lines = f.read_text().splitlines()
        imports += [x for x in lines if x.startswith("import ")]
        bodies.append("\n".join(x for x in lines if not x.startswith("import ")))
        source_hashes[str(f.relative_to(ROOT))] = sha(f)
    audit_file = directory / "component-audits.lean"
    audit_file.write_text("\n".join(dict.fromkeys(imports)) + "\n" + "\n".join(bodies))
    report: dict[str, Any] = dict(
        input_sha256=sha(args.inputs),
        references_sha256=sha(args.references) if args.references else None,
        engine=identity,
        audit_sources=source_hashes,
        source_provenance=provenance,
        selected_conductors=selected,
        selected_curve_count=sum(r["conductor"] in selected for r in rows),
        conditional_axiom=MODULARITY,
        conductors=[],
        complete=False,
        certificate_validation_version=2,
        session_started_utc=SESSION_UTC,
        previous_sessions=[],
        validator_sources={
            name: sha(ROOT / "scripts" / name)
            for name in [
                "benchmark_conductors.py",
                "conductor_validation.py",
                "conductor_status.py",
            ]
        },
    )
    previous = {}
    if (directory / "report.json").exists():
        if not args.resume:
            raise FileExistsError(
                "Report exists; use --resume or a different --output directory"
            )
        old = json.loads((directory / "report.json").read_text())
        for key in [
            "input_sha256",
            "references_sha256",
            "engine",
            "audit_sources",
            "source_provenance",
            "selected_conductors",
        ]:
            if old.get(key) != report[key]:
                raise ValueError(f"Resume identity changed: {key}")
        report["previous_sessions"] = old.get("previous_sessions", [])
        if "session_started_utc" in old:
            report["previous_sessions"].append(
                {
                    k: old[k]
                    for k in [
                        "session_started_utc",
                        "session_elapsed_seconds",
                        "validator_sources",
                    ]
                    if k in old
                }
            )
        previous = {
            r["conductor"]: r
            for r in old.get("pending_checked_conductors", []) + old["conductors"]
            if r["status"] == "checked"
        }
    report["pending_checked_conductors"] = list(previous.values())
    report["search_limits"] = {
        "central_terms_max": 128,
        "central_bits_max": 106,
        "derivative_terms_max": 128,
        "derivative_bits": 53,
        "derivative_steps_per_unit_max": 16,
        "derivative_cutoff_max": 64,
    }
    save(directory / "report.json", report)
    report["prerequisite_build_seconds"] = run(
        [
            "lake",
            "build",
            "conductor-certificates",
            "VerifiedLcalc.Assumptions.DerivativeCertification",
        ],
        directory / "prerequisites.log",
        args.timeout,
    )
    report["global_component_audit_seconds"] = run(
        ["lake", "env", "lean", str(audit_file.resolve())],
        directory / "component-audits.log",
        args.timeout,
    )
    for N in selected:
        started = time.monotonic()
        module = prefix + ".N" + str(N)
        out = directory / str(N)
        out.mkdir(parents=True, exist_ok=True)
        if N in previous:
            record: dict[str, Any] = previous[N]
            source = ROOT / (module.replace(".", "/") + ".lean")
            if sha(source) != record["source_sha256"]:
                raise ValueError("Saved proof source changed; refuse resume")
            binding_path = ROOT / ((module + "Checked").replace(".", "/") + ".lean")
            binding, required = binding_source(module, N, record["cases"], rows)
            # A legacy input-only binding is replaced by a complete typed binding.
            if (
                record.get("certificate_validation_version", 1) >= 2
                and sha(binding_path) != record["binding_sha256"]
            ):
                raise ValueError("Saved checked binding changed; refuse resume")
            if not binding_path.exists() or binding_path.read_text() != binding:
                binding_path.write_text(binding)
            elapsed = run(
                ["lake", "build", module + "Checked"], out / "resume.log", args.timeout
            )
            trace = (
                ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".trace")
            )
            messages = "\n".join(
                x["message"] for x in json.loads(trace.read_text())["log"]
            )
            audit_messages(messages, required)
            record["binding_sha256"] = sha(binding_path)
            record["certificate_validation_version"] = 2
            record.setdefault("resume_validation_seconds", []).append(elapsed)
            report["conductors"].append(record)
            report["pending_checked_conductors"] = [
                r for r in report["pending_checked_conductors"] if r["conductor"] != N
            ]
            save(directory / "report.json", report)
            print(f"Conductor {N}: revalidated checked cache in {elapsed}s", flush=True)
            continue
        record = dict(
            conductor=N,
            status="running",
            module=module,
            certificate_validation_version=2,
        )
        report["conductors"].append(record)
        save(directory / "report.json", report)
        try:
            source = ROOT / (module.replace(".", "/") + ".lean")
            olean = (
                ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            )
            record["prior_artifact_exists"] = olean.exists()
            record["producer_seconds"] = run(
                [
                    ".lake/build/bin/conductor-certificates",
                    str(args.inputs.resolve()),
                    str(N),
                    module,
                    str(out.resolve()),
                ],
                out / "producer.log",
                args.timeout,
            )
            proposal = json.loads((out / "proposals.json").read_text())
            these = [r for r in rows if r["conductor"] == N]
            expected = {r["label"]: r for r in these}
            if (
                proposal["module"] != module
                or proposal["conductor"] != N
                or len(proposal["cases"]) != len(these)
            ):
                raise ValueError("Producer changed conductor inputs")
            labels = [r["label"] for r in proposal["cases"]]
            if len(set(labels)) != len(labels) or set(labels) != set(expected):
                raise ValueError("Producer changed labels")
            # Typecheck every reported rank, component and setting against its theorem.
            binding_module = module + "Checked"
            binding_path = ROOT / (binding_module.replace(".", "/") + ".lean")
            binding, required = binding_source(module, N, proposal["cases"], rows)
            if not binding_path.exists() or binding_path.read_text() != binding:
                binding_path.write_text(binding)
            record["kernel_build_seconds"] = run(
                ["lake", "build", binding_module], out / "kernel.log", args.timeout
            )
            trace = (
                ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".trace")
            )
            messages = "\n".join(
                x["message"] for x in json.loads(trace.read_text())["log"]
            )
            audited = audit_messages(messages, required)
            save(out / "component-axioms.json", audited)
            record["audited_component_count"] = len(audited)
            record["source_sha256"] = sha(source)
            record["binding_sha256"] = sha(binding_path)
            if not args.skip_warm:
                record["warm_validation_seconds"] = run(
                    ["lake", "build", binding_module], out / "warm.log", args.timeout
                )
            results = []
            for r in proposal["cases"]:
                c = r.copy()
                rank = c.pop("proposed_rank")
                c["certified_rank"] = rank
                c["status"] = (
                    "verified-conditional-exact-rank"
                    if rank is not None
                    else c["status"]
                )
                c["reference_rank"] = refs.get(c["label"])
                c["reference_match"] = (
                    None
                    if rank is None or refs.get(c["label"]) is None
                    else rank == refs[c["label"]]
                )
                results.append(c)
            record["verified_count"] = sum(
                r["certified_rank"] is not None for r in results
            )
            record["inconclusive_count"] = len(results) - record["verified_count"]
            record["reference_mismatches"] = sum(
                r["reference_match"] is False for r in results
            )
            record["cases"] = results
            record["status"] = "checked"
            if record["reference_mismatches"]:
                raise ValueError("Reference mismatch; stop for review")
        except BaseException as error:
            record["status"] = "failed"
            record["error"] = repr(error)
            record["elapsed_seconds"] = round(time.monotonic() - started, 6)
            save(directory / "report.json", report)
            raise
        record["elapsed_seconds"] = round(time.monotonic() - started, 6)
        save(directory / "report.json", report)
        print(json.dumps({k: v for k, v in record.items() if k != "cases"}), flush=True)
    report["complete"] = True
    report["verified_count"] = sum(r["verified_count"] for r in report["conductors"])
    report["inconclusive_count"] = sum(
        r["inconclusive_count"] for r in report["conductors"]
    )
    report["reference_mismatches"] = sum(
        r["reference_mismatches"] for r in report["conductors"]
    )
    save(directory / "report.json", report)
    print("Report: " + str(directory / "report.json"), flush=True)


if __name__ == "__main__":
    main()
