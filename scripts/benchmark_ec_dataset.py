"""Generate untrusted Lean witnesses, then time kernel certification of a dataset.

Expected ranks are stripped before the Lean producer runs. Generated numerical
witnesses, source files and oleans stay in .lake; only the measurement report is
intended for version control. No mathematical computation is performed in Python.
"""

import argparse
import hashlib
import json
import multiprocessing
import os
import platform
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
from collections import Counter
from collections.abc import Callable
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.benchmark_certify_ec import LAKE, ROOT, digest, mathlib_revision

LEGACY_FACT_FIELDS = ("analytic_rank", "nonsingular", "global_minimal")
CATALOG_FACT_FIELDS = (
    *LEGACY_FACT_FIELDS,
    "arithmetic_conductor",
    "arithmetic_root_number",
    "l_function_coefficients",
    "discriminant_prime_factorization",
)


def arithmetic_catalog_values(witness: dict[str, Any]) -> dict[str, Any]:
    """Read the exact candidate literals that the Lean import must verify."""
    rank = witness["rank"]
    conductor = witness["subject"]["conductor"]
    primes = witness["arithmetic"]["minimality"]
    coefficients = witness["coefficients"]
    if (
        witness["schema"] != "lcalc.ec-rank.v1"
        or rank not in ("0", "1")
        or not isinstance(conductor, str)
        or not re.fullmatch(r"[1-9][0-9]*", conductor)
        or not isinstance(primes, list)
        or not all(
            isinstance(p, str) and re.fullmatch(r"[1-9][0-9]*", p) for p in primes
        )
        or not isinstance(coefficients, list)
        or not coefficients
        or not all(
            isinstance(c, str) and re.fullmatch(r"0|-?[1-9][0-9]*", c)
            for c in coefficients
        )
    ):
        raise ValueError("Invalid arithmetic literals in rank witness")
    values = {
        "arithmetic_conductor": int(conductor),
        "arithmetic_root_number": 1 if rank == "0" else -1,
        "l_function_coefficients": list(map(int, coefficients)),
    }
    if primes:
        values["discriminant_prime_factorization"] = list(map(int, primes))
    return values


def catalog_import_examples(
    row: dict[str, Any], subject: dict[str, Any], arithmetic: dict[str, Any]
) -> str:
    """Bind the published facts and their subject to literal values in a fresh Lean import."""
    prefix = row["declaration_prefix"]
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", prefix):
        raise ValueError("Invalid declaration prefix in proof-import check")
    coefficients = ", ".join(str(int(value)) for value in subject["ainvs"])
    conductor = int(subject["conductor"])
    rank = int(row["rank"])
    examples = (
        f"example : {prefix}.curve = (⟨{coefficients}⟩ : WeierstrassCurve ℤ) := rfl\n"
        f"example : {prefix}.result.conductor = {conductor} := rfl\n"
        f"example : {prefix}.curve.Δ ≠ 0 := {prefix}.nonsingular\n"
        f"example : WeierstrassCurve.IsGlobalMinimal (NumberField.RingOfIntegers ℚ) "
        f"({prefix}.curve.baseChange ℚ) := {prefix}.global_minimal\n"
        f"example : analyticOrderAt "
        f"(VerifiedLcalc.Modularity.modularWitness {prefix}.curve {prefix}.nonsingular).formL "
        f"(1 : ℂ) = {rank} := {prefix}.analytic_rank\n"
    )

    if arithmetic:
        level = int(arithmetic["arithmetic_conductor"])
        sign = int(arithmetic["arithmetic_root_number"])
        examples += (
            f"example : VerifiedLcalc.EllipticCurve.wildLevelFast {prefix}.curve "
            f"{prefix}.localData = {level} := {prefix}.conductor_valid\n"
            f"example : VerifiedLcalc.EllipticCurve.wildSignFast {prefix}.curve "
            f"{prefix}.localData = {sign} := {prefix}.root_number_valid\n"
        )
        values = ", ".join(map(str, map(int, arithmetic["l_function_coefficients"])))
        examples += (
            f"example : let values : List ℤ := [{values}]; "
            f"(List.range values.length).map (fun n => "
            f"({prefix}.curve.baseChange ℚ).LFunction (n + 1)) = values := "
            f"{prefix}.l_function_coefficients\n"
        )
        if "discriminant_prime_factorization" in arithmetic:
            primes = ", ".join(
                map(str, map(int, arithmetic["discriminant_prime_factorization"]))
            )
            examples += (
                f"example : VerifiedLcalc.EllipticCurve.MinimalityWitness.Valid "
                f"⟨[{primes}]⟩ {prefix}.curve := {prefix}.minimality_valid\n"
            )
    return examples


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


def selected_inputs(source: Path, count: int, offset: int = 0) -> list[dict[str, Any]]:
    """Accept legacy cases or rank-free SQL inputs; expose only input fields."""
    if count < 1 or offset < 0:
        raise ValueError("Count must be positive and offset must be nonnegative")
    data = json.loads(source.read_text())
    rows = data["inputs"] if "inputs" in data else data["cases"]
    selected = rows[offset : offset + count]
    if len(selected) != count or len({r["label"] for r in selected}) != count:
        raise ValueError("Not enough distinct source curves")
    return [
        {key: row[key] for key in ["label", "ainvs", "conductor"]} for row in selected
    ]


def reference_ranks(source: Path, references: Path | None) -> dict[str, int | None]:
    """Read reference ranks only after mathematical validation has finished."""
    if references is None:
        rows = json.loads(source.read_text())["cases"]
    else:
        rows = json.loads(references.read_text())["references"]
    if len({r["label"] for r in rows}) != len(rows):
        raise ValueError("Duplicate reference labels")
    return {r["label"]: r["analytic_rank"] for r in rows}


def stop_worker(_signum: int, _frame: object) -> None:
    # Raising through subprocess.run makes it kill and reap its Lean child.
    raise SystemExit(143)


def initialize_worker() -> None:
    signal.signal(signal.SIGTERM, stop_worker)


def validate_batch(job: dict[str, Any]) -> dict[str, Any]:
    """One process owns one output module; shared dependencies are read-only."""
    work = Path(job["work"])
    module = job["module"]
    prefix = job["prefix"]
    text = job["template"].replace(
        "ECBenchmark", f"{prefix}ECBenchmark{job['index']:04d}"
    )
    text += (
        "\n"
        + "\n".join(
            f"benchmark_ec {prefix}Curve{r['index']:04d} {json.dumps(r['label'])} "
            f"{json.dumps(str(work / 'witnesses' / r['file']))}"
            for r in job["rows"]
        )
        + "\n"
    )
    (work / f"{module}.lean").write_text(text)
    log = work / f"{module}.log"
    measurement = timed(
        [job["lean"], "-o", f"{module}.olean", f"{module}.lean"],
        work,
        job["env"],
        log,
        job["timeout"],
    )
    events = {}
    for line in log.read_text().splitlines():
        if line.startswith("EC_BENCH "):
            event = json.loads(line.removeprefix("EC_BENCH "))
            if event["label"] in events:
                raise RuntimeError("Duplicate validation event")
            events[event["label"]] = event
    measurement.update(
        {
            "batch_index": job["index"],
            "module": module,
            "labels": [r["label"] for r in job["rows"]],
        }
    )
    return {"measurement": measurement, "events": events}


def adopt_generation(
    previous: dict[str, Any],
    identity: dict[str, Any],
    inputs: list[dict[str, Any]],
    work: Path,
) -> list[dict[str, Any]]:
    """Reuse numerical candidates only; every mathematical certificate is rebuilt."""
    for key in [
        "source_sha256",
        "references_sha256",
        "mathlib_revision",
        "actual_lean_version",
        "count",
        "producer_sha256",
        "toolchain",
    ]:
        if previous["identity"].get(key) != identity.get(key):
            raise ValueError(f"Generation environment differs: {key}")
    if previous["identity"].get("offset", 0) != identity.get("offset", 0):
        raise ValueError("Generation environment differs: offset")
    # Numerical candidates are untrusted and will be rechecked. A change to the
    # proof-producing frontend does not change the producer's dependencies.
    old_core = {
        p: h
        for p, h in previous["identity"]["production_sha256"].items()
        if not p.startswith("VerifiedLcalc/Tactic/")
    }
    new_core = {
        p: h
        for p, h in identity["production_sha256"].items()
        if not p.startswith("VerifiedLcalc/Tactic/")
    }
    if old_core != new_core:
        raise ValueError("Generation mathematical or numerical core differs")
    if not previous.get("generation_complete") or len(previous["curves"]) != len(
        inputs
    ):
        raise ValueError("Previous generation is incomplete")
    old_work = (ROOT / previous["work_directory"]).resolve()
    if not old_work.is_relative_to((ROOT / ".lake").resolve()):
        raise ValueError("Generation artifacts must be under this workspace's .lake")
    target = work / "witnesses"
    target.mkdir(exist_ok=True)
    result = []
    fields = [
        "index",
        "label",
        "conductor",
        "parameters",
        "generation_seconds",
        "rank",
        "witness_sha256",
        "reason",
        "file",
    ]
    for index, (row, expected) in enumerate(
        zip(previous["curves"], inputs, strict=True)
    ):
        if row["index"] != index or row["label"] != expected["label"]:
            raise ValueError("Generation inputs changed order")
        copied = {key: row[key] for key in fields if key in row}
        copied["status"] = row["status"]
        copied["conductor"] = expected["conductor"]
        if "file" in row:
            if row["file"] != f"{index}.json":
                raise ValueError("Unexpected witness filename")
            file = old_work / "witnesses" / row["file"]
            if digest(file) != row["witness_sha256"]:
                raise ValueError("Witness hash differs")
            witness = json.loads(file.read_text())
            if (
                witness["rank"] != row["rank"]
                or witness["parameters"] != row["parameters"]
            ):
                raise ValueError(
                    "Witness claim or numerical parameters differ from generation metadata"
                )
            subject = witness["subject"]
            if [int(x) for x in subject["ainvs"]] != expected["ainvs"] or int(
                subject["conductor"]
            ) != expected["conductor"]:
                raise ValueError("Witness subject differs from input")
            shutil.copy2(file, target / row["file"])
            copied["status"] = "proposed"
        elif row["status"] not in ["inconclusive", "generation_error"]:
            raise ValueError("Generation outcome is missing its witness")
        result.append(copied)
    return result


def main() -> None:
    started = time.perf_counter()
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
        "--offset",
        type=int,
        default=0,
        help="Skip this many source rows before selection",
    )
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
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument(
        "--generation-report",
        type=Path,
        help="Reuse compatible untrusted witnesses; recheck every proof",
    )
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
        or args.workers < 1
    ):
        parser.error(
            "Count, batch size, timeout, consumer modules and workers must be positive; batch work limit must be nonnegative"
        )
    if args.module_prefix and not re.fullmatch(
        r"[A-Za-z][A-Za-z0-9_]*", args.module_prefix
    ):
        parser.error("Module prefix must be an ASCII Lean identifier prefix")
    source = args.source.resolve()
    references_path = args.references.resolve() if args.references else None
    if "inputs" in json.loads(source.read_text()) and references_path is None:
        parser.error("SQL input snapshots require --references")
    try:
        inputs = selected_inputs(source, args.count, args.offset)
    except ValueError as error:
        parser.error(str(error))
    producer = ROOT / "benchmarks/ProduceECWitnesses.lean"
    validator = ROOT / "benchmarks/ValidateEC.lean"
    mathlib = mathlib_revision()
    identity = {
        "source_sha256": digest(source),
        "references_sha256": digest(references_path) if references_path else None,
        "batch_work_limit": args.batch_work_limit,
        "module_prefix": args.module_prefix,
        "consumer_modules": args.consumer_modules,
        "workers": args.workers,
        "mathlib_revision": mathlib,
        "actual_lean_version": captured(["lean", "--version"]),
        "count": args.count,
        "offset": args.offset,
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
        "schema": "verified-lcalc.dataset-benchmark.v2",
        "identity": identity,
        "git_revision": captured(["git", "rev-parse", "HEAD"]),
        "mathlib_revision": mathlib,
        "platform": platform.platform(),
        "work_directory": str(work.relative_to(ROOT)),
        "selection": "Count contiguous source rows after offset, without rank filtering",
        "offset": args.offset,
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

    report["invocation_count"] = report.get("invocation_count", 0) + 1
    report["complete"] = False
    for key in [
        "error",
        "summary",
        "by_conductor",
        "compiled_reuse",
        "compiled_reuse_groups",
        "catalog_fact_fields",
    ]:
        report.pop(key, None)
    for row in report["curves"]:
        row.pop("reference_rank", None)
        row.pop("reference_matches", None)

    def save() -> None:
        report["wall_seconds"] = time.perf_counter() - started
        temp = output.with_suffix(".json.tmp")
        temp.write_text(json.dumps(report, indent=2) + "\n")
        temp.replace(output)

    save()
    try:
        run_benchmark(args, inputs, report, work, producer, validator, save)
    except (Exception, KeyboardInterrupt) as error:
        report["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        save()
    print(json.dumps(report["summary"], indent=2), flush=True)
    print(f"Report: {output}")


def run_benchmark(
    args: argparse.Namespace,
    inputs: list[dict[str, Any]],
    report: dict[str, Any],
    work: Path,
    producer: Path,
    validator: Path,
    save: Callable[[], None],
) -> None:
    with (work / "prebuild.log").open("w") as log:
        subprocess.run(
            [*LAKE, "build", "VerifiedLcalc.Tactic.CertifyEC"],
            cwd=ROOT,
            check=True,
            stdout=log,
            stderr=subprocess.STDOUT,
        )
    env = dict(os.environ)
    env["LEAN_PATH"] = (
        str(work) + os.pathsep + captured([*LAKE, "env", "printenv", "LEAN_PATH"])
    )
    lean = str(Path(captured(["lean", "--print-prefix"])) / "bin" / "lean")
    (work / "inputs.json").write_text(json.dumps({"inputs": inputs}) + "\n")
    generation_log = work / "generation.jsonl"
    if not report.get("generation_complete") and args.generation_report:
        origin_path = args.generation_report.resolve()
        previous = json.loads(origin_path.read_text())
        report["curves"] = adopt_generation(previous, report["identity"], inputs, work)
        report["generation"] = previous["generation"]
        report["generation_reuse"] = {
            "report_sha256": digest(origin_path),
            "original_git_revision": previous["git_revision"],
            "original_work_directory": previous["work_directory"],
            "proofs_reused": False,
            "proof_frontend_changes": {
                p: {
                    "previous": previous["identity"]["production_sha256"].get(p),
                    "current": h,
                }
                for p, h in report["identity"]["production_sha256"].items()
                if p.startswith("VerifiedLcalc/Tactic/")
                and previous["identity"]["production_sha256"].get(p) != h
            },
        }
        report["generation_complete"] = True
        save()
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
        generation_failed = report["generation"]["returncode"] != 0
        report["curves"] = []
        with generation_log.open() as log:
            for index, line in enumerate(log):
                try:
                    entry = json.loads(line)
                except json.JSONDecodeError:
                    if generation_failed:
                        break
                    raise
                if index >= len(inputs):
                    raise RuntimeError("Producer returned too many outcomes")
                row = entry["result"]
                source_row = inputs[index]
                if row["index"] != index or row["label"] != source_row["label"]:
                    raise RuntimeError("Producer changed the curve order")
                row["generation_seconds"] = entry["generation_ns"] / 1e9
                row["conductor"] = source_row["conductor"]
                if row["status"] == "proposed":
                    row["witness_sha256"] = digest(work / "witnesses" / row["file"])
                report["curves"].append(row)
        if generation_failed:
            raise RuntimeError(f"Witness generation failed: {generation_log}")
        if len(report["curves"]) != len(inputs):
            raise RuntimeError("Producer returned the wrong number of outcomes")
        report["generation_complete"] = True
        save()
    candidates = [r for r in report["curves"] if "file" in r]
    print(
        f"Proposed {len(candidates)}/{len(inputs)}; starting kernel validation.",
        flush=True,
    )
    template = validator.read_text()
    by_label = {r["label"]: r for r in report["curves"]}
    completed = {
        b["batch_index"]
        for b in report["batches"]
        if b["returncode"] == 0
        and all(by_label[label]["status"] == "checked" for label in b["labels"])
    }
    batches = numerical_batches(candidates, args.batch_size, args.batch_work_limit)
    jobs = [
        {
            "index": i,
            "module": f"{args.module_prefix}Batch{i:04d}",
            "prefix": args.module_prefix,
            "rows": batch,
            "work": str(work),
            "env": env,
            "lean": lean,
            "timeout": args.timeout,
            "template": template,
        }
        for i, batch in enumerate(batches)
        if i not in completed
    ]
    phase_start = time.perf_counter()
    phase_lean_start = lean_clock_now()
    before_phase = resource.getrusage(resource.RUSAGE_CHILDREN)
    phase: dict[str, Any] = {
        "workers": args.workers,
        "batch_indices": [],
        "complete": False,
    }
    report.setdefault("validation_phases", []).append(phase)

    def accept(result: dict[str, Any]) -> None:
        measurement, events = result["measurement"], result["events"]
        batch_index = measurement["batch_index"]
        batch = batches[batch_index]
        if events.keys() - {r["label"] for r in batch}:
            raise RuntimeError("Unexpected curve in validation output")
        succeeded = measurement["returncode"] == 0
        failure_status = (
            "timeout" if measurement["status"] == "timeout" else "batch_failed"
        )
        for row in batch:
            event = events.pop(row["label"], None)
            row.pop("error", None)
            row.pop("validation_seconds", None)
            if event:
                row["validation_seconds"] = event["validation_ns"] / 1e9
                row["status"] = event["status"] if succeeded else failure_status
                if event["error"]:
                    row["error"] = event["error"]
            else:
                row["status"] = failure_status
            row["module"] = measurement["module"]
            row["declaration_prefix"] = f"{args.module_prefix}Curve{row['index']:04d}"
        report["batches"] = [
            b for b in report["batches"] if b["batch_index"] != batch_index
        ]
        report["batches"].append(measurement)
        report["batches"].sort(key=lambda b: b["batch_index"])
        phase["batch_indices"].append(batch_index)
        phase["wall_seconds"] = time.perf_counter() - phase_start
        phase["lean_clock_elapsed_seconds"] = lean_clock_now() - phase_lean_start
        save()
        checked = sum(r["status"] == "checked" for r in by_label.values())
        print(
            f"Batch {batch_index + 1}/{len(batches)}: {measurement['wall_seconds']:.2f}s; "
            f"{checked}/{len(inputs)} checked",
            flush=True,
        )

    try:
        if args.workers == 1:
            for job in jobs:
                accept(validate_batch(job))
        else:
            with ProcessPoolExecutor(
                max_workers=args.workers,
                mp_context=multiprocessing.get_context("spawn"),
                initializer=initialize_worker,
            ) as pool:
                futures = [pool.submit(validate_batch, job) for job in jobs]
                try:
                    for future in as_completed(futures):
                        accept(future.result())
                except BaseException:
                    for future in futures:
                        future.cancel()
                    for worker in multiprocessing.active_children():
                        worker.terminate()
                    raise
        phase["complete"] = True
    finally:
        phase["wall_seconds"] = time.perf_counter() - phase_start
        phase["lean_clock_elapsed_seconds"] = lean_clock_now() - phase_lean_start
        after_phase = resource.getrusage(resource.RUSAGE_CHILDREN)
        phase["cpu_seconds"] = (
            after_phase.ru_utime
            + after_phase.ru_stime
            - before_phase.ru_utime
            - before_phase.ru_stime
        )
        save()
    checked_rows = [r for r in report["curves"] if r["status"] == "checked"]
    for row in checked_rows:
        path = work / "witnesses" / row["file"]
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != row["witness_sha256"]:
            raise RuntimeError(f"Witness bytes changed for {row['label']}")
        row["arithmetic_catalog"] = arithmetic_catalog_values(json.loads(raw))

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
                catalog_import_examples(r, inputs[r["index"]], r["arithmetic_catalog"])
                for r in group_rows
            )
        )
        name = f"{args.module_prefix}Consumer{start // args.consumer_modules:04d}"
        (work / f"{name}.lean").write_text(consumer)
        measurement = timed(
            [lean, f"{name}.lean"], work, env, work / f"{name}.log", args.timeout
        )
        measurement.update({"modules": group_modules, "curves": len(group_rows)})
        if measurement["returncode"] == 0:
            measurement["module_sha256"] = {
                module: digest(work / f"{module}.olean") for module in group_modules
            }
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
    report["catalog_fact_fields"] = CATALOG_FACT_FIELDS
    # References enter only after all mathematical checks have finished.
    references = reference_ranks(args.source, args.references)
    for row in checked_rows:
        row["reference_rank"] = references[row["label"]]
        row["reference_matches"] = (
            int(row["rank"]) == row["reference_rank"]
            if row["reference_rank"] is not None
            else None
        )
    durations = [r["validation_seconds"] for r in checked_rows]
    total = sum(p["wall_seconds"] for p in report["validation_phases"])
    report["summary"] = {
        "outcomes": dict(Counter(r["status"] for r in report["curves"])),
        "inconclusive_reasons": dict(
            Counter(r["reason"] for r in report["curves"] if "reason" in r)
        ),
        "validation_phase_wall_seconds": total,
        "sum_batch_wall_seconds": sum(b["wall_seconds"] for b in report["batches"]),
        "validation_phase_cpu_seconds": sum(
            p["cpu_seconds"] for p in report["validation_phases"]
        ),
        "validation_timing_complete": all(
            p["complete"] for p in report["validation_phases"]
        ),
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
        "reference_agreements": sum(
            r["reference_matches"] is True for r in checked_rows
        ),
        "reference_mismatches": sum(
            r["reference_matches"] is False for r in checked_rows
        ),
        "reference_unknown": sum(r["reference_matches"] is None for r in checked_rows),
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
    failures = {
        status: count
        for status, count in report["summary"]["outcomes"].items()
        if status not in {"checked", "inconclusive"}
    }
    if failures:
        raise RuntimeError(f"Benchmark failed with outcomes {failures}; logs: {work}")
    if report["summary"]["reference_mismatches"]:
        raise RuntimeError(f"Checked ranks differ from references; logs: {work}")
    report["complete"] = True


if __name__ == "__main__":
    main()
