"""Locate Lean proof dependencies without requiring a candidate-generator binary."""

import json
import os
from pathlib import Path

from lcalc_registry.checker.environment import compatibility_manifest
from lcalc_registry.checker.protocol import digest

from .config import Settings
from .contracts import ProofEnvironment


def installed(settings: Settings) -> ProofEnvironment:
    root = settings.checker_root.resolve()
    specification = (root / "lean-toolchain").read_text().strip()
    binary = (
        Path.home()
        / ".elan/toolchains"
        / specification.replace("/", "--").replace(":", "---")
        / "bin/lean"
    )
    config = (settings.worker_build or root / "worker/build") / "environment.json"
    if config.exists():
        binary = Path(json.loads(config.read_text())["lean_bin"])
    paths = [
        root / ".lake/build/lib/lean",
        root.parent / "mathlib4/.lake/build/lib/lean",
    ]
    paths.extend((root / ".lake/packages").glob("*/.lake/build/lib/lean"))
    manifest = compatibility_manifest(root, binary)
    return ProofEnvironment(
        id=digest(manifest),
        public=manifest,
        lean=binary,
        lean_path=os.pathsep.join(map(str, paths)),
    )
