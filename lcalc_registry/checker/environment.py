import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

from .contracts import EnvironmentManifest
from .protocol import digest

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "worker"


def file_hash(path: Path | str) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def compatibility_manifest(
    root: Path, lean: Path, mathlib: Path | None = None
) -> EnvironmentManifest:
    root = Path(root).resolve()
    files = {
        str(p.relative_to(root)): file_hash(p)
        for p in sorted((root / "VerifiedLcalc").rglob("*.lean"))
        if "Certificates" not in p.parts and not p.name.startswith("Generated")
    }
    version = subprocess.run(
        [str(lean), "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()
    lock = json.loads((root / "lake-manifest.json").read_text())
    if mathlib is None:
        candidates = [root / ".lake/packages/mathlib", root.parent / "mathlib4"]
        package = next((p for p in lock["packages"] if p["name"] == "mathlib"), {})
        if package.get("dir"):
            candidates.insert(0, root / package["dir"])
        mathlib = next((p for p in candidates if p.exists()), None)
    if mathlib is None:
        raise RuntimeError("Specify the installed mathlib root")
    revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=mathlib,
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    tau = next(
        (
            p.get("rev")
            for p in lock["packages"]
            if p["name"].lower() in ["tauceti", "tau_ceti"]
        ),
        None,
    )
    return {
        "schema": "lcalc.environment.v1",
        "lean": version,
        "mathlib": revision,
        "tau_ceti": tau,
        "platform": {
            "system": platform.system(),
            "machine": platform.machine(),
            "word_bits": 64 if sys.maxsize > 2**32 else 32,
        },
        "checker_sources": files,
        "modularity_statement_sha256": files[
            "VerifiedLcalc/Assumptions/ModularityStatement.lean"
        ],
    }


class Environment:
    def __init__(self, root: Path = ROOT, build: Path = BASE / "build") -> None:
        self.root = Path(root).resolve()
        self.build = Path(build).resolve()
        self.build_config = json.loads((self.build / "environment.json").read_text())
        self.lean = Path(self.build_config["lean_bin"])
        self.worker = self.build / "certificate-worker"
        self.lean_path = self.build_config["lean_path"]
        self.worker_hash = file_hash(self.worker)
        self.public = compatibility_manifest(self.root, self.lean)
        self.files = self.public["checker_sources"]
        self.id = digest(self.public)
        self.implementation = {
            "worker_sha256": self.worker_hash,
            "source_template_sha256": file_hash(
                self.root / "worker/lean/LcalcVolunteer/Source.lean"
            ),
        }

    def check_immutable(self) -> None:
        if file_hash(self.worker) != self.worker_hash or any(
            file_hash(self.root / p) != h for p, h in self.files.items()
        ):
            raise RuntimeError(
                "Registered validation environment changed; register a new profile"
            )
