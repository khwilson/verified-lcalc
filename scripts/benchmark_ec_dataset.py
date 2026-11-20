"""Generate untrusted Lean witnesses, then time kernel certification of a dataset.

Expected ranks are stripped before the Lean producer runs. Generated numerical
witnesses, source files and oleans stay in .lake; only the measurement report is
intended for version control. No mathematical computation is performed in Python.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import resource
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_certify_ec import LAKE, ROOT, digest


def captured(args: list[str]) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def lean_clock_now() -> float:
    # Apple's libc++ steady_clock uses CLOCK_MONOTONIC_RAW, unlike Python's
    # mach_absolute_time-based perf_counter. Record both instead of conflating
    # system suspension with computation time.
    if sys.platform == "darwin":
        return time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
    return time.perf_counter()


def timed(
    args: list[str], cwd: Path, env: dict[str, str], log: Path, timeout: int
) -> dict[str, Any]:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start_lean_clock = lean_clock_now()
    start = time.perf_counter()
    status = "finished"
    with log.open("w") as stream:
        try:
            result = subprocess.run(
                args,
                cwd=cwd,
                env=env,
                stdout=stream,
                stderr=subprocess.STDOUT,
                timeout=timeout,
                check=False,
            )
            code = result.returncode
        except subprocess.TimeoutExpired:
            code, status = None, "timeout"
    elapsed = time.perf_counter() - start
    lean_elapsed = lean_clock_now() - start_lean_clock
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {
        "status": status,
        "returncode": code,
        "wall_seconds": elapsed,
        "lean_clock_elapsed_seconds": lean_elapsed,
        "cpu_seconds": after.ru_utime
        + after.ru_stime
        - before.ru_utime
        - before.ru_stime,
    }


def quantile(values: list[float], fraction: float) -> float | None:
    if not values:
        return None
    values = sorted(values)
    return values[round((len(values) - 1) * fraction)]


def numerical_batches(
    rows: list[dict[str, Any]],
    size: int,
    work_limit: int,
) -> list[list[dict[str, Any]]]:
    """Bound batches using supplied numerical parameters, never reference ranks."""
    batches: list[list[dict[str, Any]]] = []
    batch: list[dict[str, Any]] = []
    work = 0
    for row in rows:
        parameters = row["parameters"]
        terms = int(parameters["terms"])
        steps = int(parameters["steps_per_unit"])
        cutoff = int(parameters["cutoff"])
        cost = terms * max(1, steps * (cutoff - 1))
        if batch and (len(batch) >= size or (work_limit and work + cost > work_limit)):
            batches.append(batch)
            batch, work = [], 0
        batch.append(row)
        work += cost
    if batch:
        batches.append(batch)
    return batches


def selected_inputs(source: Path, count: int) -> list[dict[str, Any]]:
    """Accept legacy cases or rank-free SQL inputs; expose only input fields."""
    data = json.loads(source.read_text())
    rows = data["inputs"] if "inputs" in data else data["cases"]
    selected = rows[:count]
    if len(selected) != count or len({r["label"] for r in selected}) != count:
        raise ValueError("Not enough distinct source curves")
    return [
        {key: row[key] for key in ["label", "ainvs", "conductor"]} for row in selected
    ]


def reference_ranks(source: Path, references: Path | None) -> dict[str, int]:
    """Read reference ranks only after mathematical validation has finished."""
    if references is None:
        rows = json.loads(source.read_text())["cases"]
    else:
        rows = json.loads(references.read_text())["references"]
    if len({r["label"] for r in rows}) != len(rows):
        raise ValueError("Duplicate reference labels")
    return {r["label"]: r["analytic_rank"] for r in rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source", type=Path, default=ROOT / "data/lmfdb-1000-additional.json"
    )
    parser.add_argument(
        "--references",
        type=Path,
        help="Separate rank references, required for SQL inputs",
    )
    parser.add_argument(
        "--module-prefix",
        default="",
        help="Unique Lean module/declaration prefix for importing several datasets",
    )
    parser.add_argument("--count", type=int, default=1000)
    parser.add_argument(
        "--batch-work-limit",
        type=int,
        default=0,
        help="Cap terms*steps*(cutoff-1) per batch; 0 disables this cap",
    )
    parser.add_argument(
        "--consumer-modules",
        type=int,
        default=25,
        help="Maximum compiled batch modules per proof-import check",
    )
    parser.add_argument("--batch-size", type=int, default=20)
    parser.add_argument("--timeout", type=int, default=900, help="Seconds per batch")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "output/certify-ec-performance/dataset-1000.json",
    )
    args = parser.parse_args()
    if (
        args.count < 1
        or args.batch_size < 1
        or args.timeout < 1
        or args.consumer_modules < 1
        or args.batch_work_limit < 0
    ):
        parser.error("Count, batch size and timeout must be positive")
    if args.module_prefix and not re.fullmatch(
        r"[A-Za-z][A-Za-z0-9_]*", args.module_prefix
    ):
        parser.error("Module prefix must be an ASCII Lean identifier prefix")
    source = args.source.resolve()
    references_path = args.references.resolve() if args.references else None
    if "inputs" in json.loads(source.read_text()) and references_path is None:
        parser.error("SQL input snapshots require --references")
    try:
        inputs = selected_inputs(source, args.count)
    except ValueError as error:
        parser.error(str(error))
    producer = ROOT / "benchmarks/ProduceECWitnesses.lean"
    validator = ROOT / "benchmarks/ValidateEC.lean"
    identity = {
        "source_sha256": digest(source),
        "references_sha256": digest(references_path) if references_path else None,
        "batch_work_limit": args.batch_work_limit,
        "module_prefix": args.module_prefix,
        "consumer_modules": args.consumer_modules,
        "mathlib_revision": captured(
            ["git", "-C", str(ROOT.parent / "mathlib4"), "rev-parse", "HEAD"]
        ),
        "actual_lean_version": captured(["lean", "--version"]),
        "count": args.count,
        "batch_size": args.batch_size,
        "timeout": args.timeout,
        "producer_sha256": digest(producer),
        "runner_sha256": digest(Path(__file__)),
        "validator_sha256": digest(validator),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "production_sha256": {
            str(p.relative_to(ROOT)): digest(p)
            for p in sorted((ROOT / "VerifiedLcalc").rglob("*.lean"))
        },
    }
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()[:16]
    work = ROOT / ".lake" / f"ec-dataset-{key}"
    work.mkdir(parents=True, exist_ok=True)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    report: dict[str, Any] = {
        "schema": "verified-lcalc.dataset-benchmark.v1",
        "identity": identity,
        "git_revision": captured(["git", "rev-parse", "HEAD"]),
        "mathlib_revision": captured(
            ["git", "-C", str(ROOT.parent / "mathlib4"), "rev-parse", "HEAD"]
        ),
        "platform": platform.platform(),
        "work_directory": str(work.relative_to(ROOT)),
        "selection": "First count source rows, without rank filtering",
        "timing_clocks": {
            "batch_wall_seconds": time.get_clock_info("perf_counter").implementation,
            "command_seconds": "Lean std::chrono::steady_clock; includes suspend on macOS",
            "lean_clock_elapsed_seconds": "CLOCK_MONOTONIC_RAW on macOS; perf_counter otherwise",
            "note": "Batch wall_seconds excludes system suspension on macOS; command timings do not",
        },
        "curves": [],
        "batches": [],
        "complete": False,
    }
    if args.resume and output.exists():
        report = json.loads(output.read_text())
        if report["identity"] != identity:
            parser.error("Resume fingerprints differ; use a new output")
    elif output.exists():
        parser.error("Output exists; use --resume or a different output")

    def save() -> None:
        temp = output.with_suffix(".json.tmp")
        temp.write_text(json.dumps(report, indent=2) + "\n")
        temp.replace(output)

    subprocess.run(
        [*LAKE, "build", "VerifiedLcalc.Tactic.CertifyEC"],
        cwd=ROOT,
        check=True,
        stdout=(work / "prebuild.log").open("w"),
        stderr=subprocess.STDOUT,
    )
    env = dict(os.environ)
    env["LEAN_PATH"] = (
        str(work) + os.pathsep + captured([*LAKE, "env", "printenv", "LEAN_PATH"])
    )
    lean = str(Path(captured(["lean", "--print-prefix"])) / "bin" / "lean")
    (work / "inputs.json").write_text(json.dumps({"inputs": inputs}) + "\n")
    generation_log = work / "generation.jsonl"
    if not report.get("generation_complete"):
        print(
            f"Generating witnesses for {len(inputs)} rank-blind inputs...", flush=True
        )
        report["generation"] = timed(
            [
                lean,
                "--run",
                str(producer),
                str(work / "inputs.json"),
                str(work / "witnesses"),
            ],
            ROOT,
            env,
            generation_log,
            max(args.timeout, 3600),
        )
        if report["generation"]["returncode"] != 0:
            save()
            raise RuntimeError(f"Witness generation failed: {generation_log}")
        generated = [
            json.loads(line) for line in generation_log.read_text().splitlines()
        ]
        if len(generated) != len(inputs):
            raise RuntimeError("Producer returned the wrong number of outcomes")
        report["curves"] = []
        for entry, source_row in zip(generated, inputs, strict=True):
            row = entry["result"]
            if row["label"] != source_row["label"]:
                raise RuntimeError("Producer changed the curve order")
            row["generation_seconds"] = entry["generation_ns"] / 1e9
            row["conductor"] = source_row["conductor"]
            if row["status"] == "proposed":
                row["witness_sha256"] = digest(work / "witnesses" / row["file"])
            report["curves"].append(row)
        report["generation_complete"] = True
        save()
    candidates = [r for r in report["curves"] if "file" in r]
    print(
        f"Proposed {len(candidates)}/{len(inputs)}; starting kernel validation.",
        flush=True,
    )
    template = validator.read_text()
    by_label = {r["label"]: r for r in report["curves"]}
    completed = len(report["batches"])
    batches = numerical_batches(candidates, args.batch_size, args.batch_work_limit)
    for batch_index, batch in enumerate(batches):
        if batch_index < completed:
            continue
        module = f"{args.module_prefix}Batch{batch_index:04d}"
        text = (
            template.replace(
                "ECBenchmark", f"{args.module_prefix}ECBenchmark{batch_index:04d}"
            )
            + "\n"
            + "\n".join(
                f"benchmark_ec {args.module_prefix}Curve{r['index']:04d} {json.dumps(r['label'])} "
                f"{json.dumps(str(work / 'witnesses' / r['file']))}"
                for r in batch
            )
            + "\n"
        )
        (work / f"{module}.lean").write_text(text)
        log = work / f"{module}.log"
        measurement = timed(
            [lean, "-o", f"{module}.olean", f"{module}.lean"],
            work,
            env,
            log,
            args.timeout,
        )
        events = {}
        for line in log.read_text().splitlines():
            if line.startswith("EC_BENCH "):
                event = json.loads(line.removeprefix("EC_BENCH "))
                if event["label"] in events:
                    raise RuntimeError("Duplicate validation event")
                events[event["label"]] = event
        succeeded = measurement["returncode"] == 0
        for row in batch:
            event = events.pop(row["label"], None)
            if event:
                row["validation_seconds"] = event["validation_ns"] / 1e9
                row["status"] = event["status"] if succeeded else "batch_failed"
                if event["error"]:
                    row["error"] = event["error"]
            else:
                row["status"] = (
                    "timeout" if measurement["status"] == "timeout" else "batch_failed"
                )
            row["module"] = module
            row["declaration_prefix"] = f"{args.module_prefix}Curve{row['index']:04d}"
        if events:
            raise RuntimeError("Unexpected curve in validation output")
        measurement.update({"module": module, "labels": [r["label"] for r in batch]})
        report["batches"].append(measurement)
        save()
        checked = sum(r["status"] == "checked" for r in by_label.values())
        print(
            f"Batch {batch_index + 1}: {measurement['wall_seconds']:.2f}s; "
            f"{checked}/{len(inputs)} checked",
            flush=True,
        )
    checked_rows = [r for r in report["curves"] if r["status"] == "checked"]
    modules = sorted({r["module"] for r in checked_rows})
    reuse_groups = []
    for start in range(0, len(modules), args.consumer_modules):
        group_modules = modules[start : start + args.consumer_modules]
        group_rows = [r for r in checked_rows if r["module"] in group_modules]
        consumer = (
            "module\n"
            + "".join(f"import {m}\n" for m in group_modules)
            + "\n"
            + "".join(
                f"example := {r['declaration_prefix']}.analytic_rank\n"
                for r in group_rows
            )
        )
        name = f"{args.module_prefix}Consumer{start // args.consumer_modules:04d}"
        (work / f"{name}.lean").write_text(consumer)
        measurement = timed(
            [lean, f"{name}.lean"], work, env, work / f"{name}.log", args.timeout
        )
        measurement.update({"modules": group_modules, "curves": len(group_rows)})
        reuse_groups.append(measurement)
        report["compiled_reuse_groups"] = reuse_groups
        save()
        if measurement["returncode"] != 0:
            raise RuntimeError(f"Compiled proof reuse failed: {work / f'{name}.log'}")
    report["compiled_reuse"] = {
        "returncode": 0,
        "curves": sum(g["curves"] for g in reuse_groups),
        "wall_seconds": sum(g["wall_seconds"] for g in reuse_groups),
        "cpu_seconds": sum(g["cpu_seconds"] for g in reuse_groups),
        "groups": len(reuse_groups),
    }
    # References enter only after all mathematical checks have finished.
    references = reference_ranks(source, references_path)
    for row in checked_rows:
        row["reference_rank"] = references[row["label"]]
        row["reference_matches"] = int(row["rank"]) == row["reference_rank"]
    durations = [r["validation_seconds"] for r in checked_rows]
    total = sum(b["wall_seconds"] for b in report["batches"])
    report["summary"] = {
        "outcomes": dict(Counter(r["status"] for r in report["curves"])),
        "inconclusive_reasons": dict(
            Counter(r["reason"] for r in report["curves"] if "reason" in r)
        ),
        "validation_batch_wall_seconds": total,
        "validation_batch_cpu_seconds": sum(
            b["cpu_seconds"] for b in report["batches"]
        ),
        "validation_wall_seconds_per_checked_curve": total / len(checked_rows)
        if checked_rows
        else None,
        "command_validation_seconds": {
            "sum": sum(durations),
            "p50": quantile(durations, 0.5),
            "p95": quantile(durations, 0.95),
            "max": max(durations, default=None),
        },
        "reference_mismatches": sum(not r["reference_matches"] for r in checked_rows),
        "compiled_olean_bytes": sum(
            (work / f"{m}.olean").stat().st_size for m in modules
        ),
    }
    report["by_conductor"] = []
    for conductor in sorted({r["conductor"] for r in report["curves"]}):
        group = [r for r in report["curves"] if r["conductor"] == conductor]
        report["by_conductor"].append(
            {
                "conductor": conductor,
                "selected": len(group),
                "outcomes": dict(Counter(r["status"] for r in group)),
                "validation_seconds": sum(
                    r.get("validation_seconds", 0) for r in group
                ),
                "reference_mismatches": sum(
                    r.get("reference_matches") is False for r in group
                ),
            }
        )
    report["complete"] = True
    save()
    print(json.dumps(report["summary"], indent=2), flush=True)
    print(f"Report: {output}")


if __name__ == "__main__":
    main()
