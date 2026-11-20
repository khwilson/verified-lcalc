"""Time fresh Lean checking, compiled-theorem reuse, and warm Lake reuse separately.

This is process orchestration only. Witness interpretation, computation and proofs
remain in Lean. Dependencies are built once before measurements; "fresh" means a
new Lean process and source check, not an emptied operating-system file cache.
"""

import argparse
import hashlib
import json
import os
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


def run(args: list[str], log: Path, env: dict[str, str] | None = None) -> Sample:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    started = time.perf_counter()
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, env=env)
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


def measure(
    args: list[str],
    label: str,
    repetitions: int,
    logs: Path,
    env: dict[str, str] | None = None,
) -> Measurement:
    samples = [run(args, logs / f"{label}-{i}.log", env) for i in range(repetitions)]
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
    parser.add_argument(
        "--launcher",
        choices=["lake", "direct"],
        default="lake",
        help="Direct resolves LEAN_PATH once, then starts Lean without Lake",
    )
    parser.add_argument(
        "--profile",
        action="store_true",
        help="Collect a separate, untimed kernel profile for each curve",
    )
    parser.add_argument(
        "--cases",
        nargs="+",
        choices=[
            "bare",
            "import_only",
            "cached_proof",
            "11a1",
            "37a1",
            "112a2",
            "batch",
            "warm_lake",
        ],
        help="Select measurements; default runs every case",
    )
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    output: Path = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    logs = output.parent / (output.stem + "-logs")
    logs.mkdir(parents=True, exist_ok=True)
    run([*LAKE, "build", "CertifiedCurves"], logs / "prebuild.log")
    results: dict[str, Measurement] = {}
    env = None
    lean = [*LAKE, "env", "lean"]
    if args.launcher == "direct":
        env = dict(os.environ)
        env["LEAN_PATH"] = captured([*LAKE, "env", "printenv", "LEAN_PATH"])
        lean = [str(Path(captured(["lean", "--print-prefix"])) / "bin" / "lean")]
    report = {
        "schema": "verified-lcalc.certify-ec-benchmark.v2",
        "description": "Fresh processes; existing dependency artifacts; OS caches not flushed",
        "repetitions": args.repetitions,
        "launcher": args.launcher,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_revision": captured(
            ["git", "-C", str(ROOT.parent / "mathlib4"), "rev-parse", "HEAD"]
        ),
        "git_revision": captured(["git", "rev-parse", "HEAD"]),
        "git_diff_sha256": hashlib.sha256(
            captured(["git", "diff"]).encode()
        ).hexdigest(),
        "platform": platform.platform(),
        "command_sha256": digest(ROOT / "VerifiedLcalc/Tactic/CertifyEC.lean"),
        "interval_core_sha256": digest(
            ROOT / "VerifiedLcalc/Numerics/RealIntervalCore.lean"
        ),
        "source_sha256": {
            str(path.relative_to(ROOT)): digest(path)
            for path in sorted((ROOT / "VerifiedLcalc").rglob("*.lean"))
        },
        "results": results,
    }

    def save() -> None:
        output.write_text(json.dumps(report, indent=2) + "\n")

    inputs = {
        label: ROOT / "data/witnesses" / f"{label}.json"
        for label in ["11a1", "37a1", "112a2"]
    }
    (ROOT / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="certify-ec-bench-", dir=ROOT / ".lake"
    ) as tmp:
        work = Path(tmp)
        sources = {"bare": "module\n", "import_only": HEADER, "cached_proof": CONSUMER}
        for label, path in inputs.items():
            sources[label] = (
                HEADER
                + 'certify_ec Bench from_json_string r#"'
                + path.read_text()
                + '"#\n'
            )
        sources["batch"] = HEADER + "".join(
            "certify_ec Bench"
            + str(i)
            + ' from_json_string r#"'
            + path.read_text()
            + '"#\n'
            for i, path in enumerate(inputs.values())
        )
        report["witness_sha256"] = {
            label: digest(path) for label, path in inputs.items()
        }
        report["batch_curves"] = list(inputs)
        for label, source in sources.items():
            if args.cases and label not in args.cases:
                continue
            file = work / (label + ".lean")
            file.write_text(source)
            results[label] = measure(
                [
                    *lean,
                    "-o",
                    str(file.with_suffix(".olean")),
                    str(file),
                ],
                label,
                args.repetitions,
                logs,
                env,
            )
            save()
        if args.profile:
            for label in inputs:
                if args.cases and label not in args.cases:
                    continue
                file = work / (label + "-profile.lean")
                file.write_text(
                    sources[label].replace(
                        HEADER,
                        HEADER
                        + "set_option profiler true\nset_option trace.profiler true\n"
                        + "set_option trace.profiler.threshold 10\n",
                    )
                )
                run([*lean, str(file)], logs / f"{label}-profile.log", env)
        if not args.cases or "warm_lake" in args.cases:
            results["warm_lake"] = measure(
                [*LAKE, "build", "CertifiedCurves"], "warm_lake", args.repetitions, logs
            )
    if "batch" in results:
        report["batch_wall_seconds_per_curve"] = results["batch"][
            "median_wall_seconds"
        ] / len(inputs)
    save()
    print(f"Report: {output}")


if __name__ == "__main__":
    main()
