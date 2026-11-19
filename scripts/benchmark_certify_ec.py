"""Time fresh Lean checking, compiled-theorem reuse, and warm Lake reuse separately.

This is process orchestration only. Witness interpretation, computation and proofs
remain in Lean. Dependencies are built once before measurements; "fresh" means a
new Lean process and source check, not an emptied operating-system file cache.
"""

import argparse
import hashlib
import json
import platform
import resource
import statistics
import subprocess
import tempfile
import time
from pathlib import Path
from typing import TypedDict

ROOT = Path(__file__).resolve().parents[1]
LAKE = ["lake", "-f", "lakefile.certificates.lean"]
HEADER = """module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
"""
CONSUMER = """module
public import CertifiedCurves.Json
@[expose] public section
open VerifiedLcalc VerifiedLcalc.Modularity

theorem reused_rank :
    analyticOrderAt (modularWitness Curve37.curve Curve37.nonsingular).formL
      (1 : ℂ) = 1 := Curve37.analytic_rank
"""


class Sample(TypedDict):
    wall_seconds: float
    cpu_seconds: float


class Measurement(TypedDict):
    samples: list[Sample]
    median_wall_seconds: float
    median_cpu_seconds: float


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def captured(args: list[str]) -> str:
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def run(args: list[str], log: Path) -> Sample:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter()
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    wall = time.perf_counter() - started
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    log.write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"Lean command failed; see {log}")
    return {
        "wall_seconds": wall,
        "cpu_seconds": after.ru_utime
        + after.ru_stime
        - before.ru_utime
        - before.ru_stime,
    }


def measure(args: list[str], label: str, repetitions: int, logs: Path) -> Measurement:
    samples = [run(args, logs / f"{label}-{i}.log") for i in range(repetitions)]
    value: Measurement = {
        "samples": samples,
        "median_wall_seconds": statistics.median(s["wall_seconds"] for s in samples),
        "median_cpu_seconds": statistics.median(s["cpu_seconds"] for s in samples),
    }
    print(
        f"{label}: {value['median_wall_seconds']:.3f}s wall, "
        f"{value['median_cpu_seconds']:.3f}s CPU (median)",
        flush=True,
    )
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    output: Path = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    logs = output.parent / (output.stem + "-logs")
    logs.mkdir(parents=True, exist_ok=True)
    run([*LAKE, "build", "CertifiedCurves"], logs / "prebuild.log")
    results: dict[str, Measurement] = {}
    inputs = {
        label: ROOT / "data/witnesses" / f"{label}.json"
        for label in ["11a1", "37a1", "112a2"]
    }
    (ROOT / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="certify-ec-bench-", dir=ROOT / ".lake"
    ) as tmp:
        work = Path(tmp)
        sources = {"import_only": HEADER, "cached_proof": CONSUMER}
        for label, path in inputs.items():
            sources[label] = (
                HEADER
                + 'certify_ec Bench from_json_string r#"'
                + path.read_text()
                + '"#\n'
            )
        for label, source in sources.items():
            file = work / (label + ".lean")
            file.write_text(source)
            results[label] = measure(
                [
                    *LAKE,
                    "env",
                    "lean",
                    "-o",
                    str(file.with_suffix(".olean")),
                    str(file),
                ],
                label,
                args.repetitions,
                logs,
            )
        results["warm_lake"] = measure(
            [*LAKE, "build", "CertifiedCurves"], "warm_lake", args.repetitions, logs
        )
    report = {
        "schema": "verified-lcalc.certify-ec-benchmark.v1",
        "description": "Fresh processes; existing dependency artifacts; OS caches not flushed",
        "repetitions": args.repetitions,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_revision": captured(
            ["git", "-C", str(ROOT.parent / "mathlib4"), "rev-parse", "HEAD"]
        ),
        "git_revision": captured(["git", "rev-parse", "HEAD"]),
        "platform": platform.platform(),
        "command_sha256": digest(ROOT / "VerifiedLcalc/Tactic/CertifyEC.lean"),
        "witness_sha256": {label: digest(path) for label, path in inputs.items()},
        "results": results,
    }
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Report: {output}")


if __name__ == "__main__":
    main()
