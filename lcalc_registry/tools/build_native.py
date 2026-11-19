#!/usr/bin/env python3
"""Compile only the new worker; reuse immutable, already-built dependencies.
This avoids a second Lake build while the conductor campaign is running.
"""

import json
import os
import re
import subprocess
import sys
from collections.abc import Sequence
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "worker"
SOURCE = BASE / "lean"
BUILD = BASE / "build"
toolchain = (
    (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
)
BIN = Path.home() / ".elan/toolchains" / toolchain / "bin"
paths = [
    str(ROOT / ".lake/build/lib/lean"),
    str(ROOT.parent / "mathlib4/.lake/build/lib/lean"),
]
paths += [str(p) for p in (ROOT / ".lake/packages").glob("*/.lake/build/lib/lean")]
paths.insert(0, str(BUILD / "lib/lean"))
ENV = {**os.environ, "LEAN_PATH": ":".join(paths), "LEAN_NUM_THREADS": "1"}


def run(args: Sequence[str | Path], cwd: Path = SOURCE) -> None:
    subprocess.run([str(x) for x in args], cwd=cwd, env=ENV, check=True)


def main() -> None:
    BUILD.mkdir(parents=True, exist_ok=True)
    objects = []
    for name in [
        "LcalcVolunteer.Core",
        "LcalcVolunteer.Source",
        "LcalcVolunteer.Witness",
        "WorkerMain",
    ]:
        relative = Path(name.replace(".", "/"))
        target = BUILD / "lib/lean" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        c = target.with_suffix(".c")
        obj = target.with_suffix(".o")
        run(
            [
                BIN / "lean",
                "-o",
                target.with_suffix(".olean"),
                "-i",
                target.with_suffix(".ilean"),
                "-c",
                c,
                SOURCE / relative.with_suffix(".lean"),
            ]
        )
        run([BIN / "leanc", "-O3", "-c", c, "-o", obj])
        objects.append(obj)
    # The runtime closure contains no mathematical proof modules or elaborator.
    seen = set()
    deps = []

    def visit(module: str) -> None:
        if module in seen or not module.startswith("VerifiedLcalc."):
            return
        seen.add(module)
        source = ROOT / Path(module.replace(".", "/")).with_suffix(".lean")
        for line in source.read_text().splitlines():
            m = re.fullmatch(r"(?:public )?import (\S+)", line.strip())
            if m:
                visit(m[1])
        obj = (
            ROOT
            / ".lake/build/ir"
            / Path(module.replace(".", "/")).with_suffix(".c.o.export")
        )
        if not obj.exists():
            raise FileNotFoundError(f"Build the existing core first: {obj}")
        deps.append(obj)

    visit("VerifiedLcalc.EllipticCurve.DerivativeCore")
    visit("VerifiedLcalc.EllipticCurve.WildRootCore")
    run(
        [
            BIN / "leanc",
            "-O3",
            "-o",
            BUILD / "certificate-worker",
            *objects,
            *deps,
            *(
                ["-Wl,-dead_strip"]
                if sys.platform == "darwin"
                else ["-Wl,--gc-sections"]
            ),
        ]
    )
    (BUILD / "environment.json").write_text(
        json.dumps(
            {
                "lean_bin": str(BIN / "lean"),
                "lean_path": ENV["LEAN_PATH"],
                "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                "core_objects": [str(p) for p in deps],
            },
            indent=2,
        )
        + "\n"
    )
    print(BUILD / "certificate-worker")


if __name__ == "__main__":
    main()
