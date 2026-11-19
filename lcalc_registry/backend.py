"""Trusted adapter to existing Lean search, proof templates and kernel checker."""

import fcntl
import json
import subprocess
import tempfile
from pathlib import Path

from lcalc_registry.checker.contracts import CacheManifest, Certificate, CurveSubject
from lcalc_registry.checker.environment import Environment, file_hash
from lcalc_registry.checker.kernel import KernelChecker, bindings
from lcalc_registry.checker.protocol import Invalid, certificate, command_line, digest

from .checker.witness import render_source
from .config import Settings
from .contracts import Generated
from .models import ProofVersion


class Inconclusive(Exception):
    pass


class NativeBackend:
    def __init__(self, settings: Settings) -> None:
        root = settings.checker_root.resolve()
        build = settings.worker_build or root / "worker/build"
        self.environment = Environment(root=root, build=build)
        self.settings = settings
        self.id = self.environment.id
        self.manifest = self.environment.public
        self.implementation = {
            **self.environment.implementation,
            "lean_binary_sha256": file_hash(self.environment.lean),
            "bindings_sha256": file_hash(root / "lcalc_registry/checker/kernel.py"),
            "witness_transport_sha256": file_hash(
                root / "lcalc_registry/checker/witness.py"
            ),
        }

    def _immutable(self) -> None:
        self.environment.check_immutable()
        if (
            file_hash(self.settings.checker_root / "lcalc_registry/checker/witness.py")
            != self.implementation["witness_transport_sha256"]
        ):
            raise Invalid("Installed witness transport changed")
        if (
            file_hash(self.environment.lean)
            != self.implementation["lean_binary_sha256"]
            or file_hash(
                self.settings.checker_root / "lcalc_registry/checker/kernel.py"
            )
            != self.implementation["bindings_sha256"]
        ):
            raise Invalid(
                "Installed checker changed; register a new validation environment"
            )

    def generate(self, subject: CurveSubject) -> Generated:
        self._immutable()
        env = self.environment
        value = json.loads(
            subprocess.check_output(
                [str(env.worker), "compute", command_line(subject)],
                text=True,
                timeout=self.settings.check_timeout_seconds,
            )
        )
        if value.get("status") == "inconclusive":
            raise Inconclusive(
                "The current arithmetic/numerical profile cannot certify this curve"
            )
        value = certificate(value)
        if value["subject"] != subject:
            raise Invalid("Generator changed the requested curve")
        return self.render(value)

    def render(self, payload: Certificate) -> Generated:
        """Generate unchecked source from the exact supplied witness; never search."""
        self._immutable()
        payload = certificate(payload)
        module = f"LcalcCertificates.C{digest(payload)}_E{self.id}"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "candidate.lean"
            source = render_source(
                self.environment,
                payload,
                module,
                path,
                self.settings.check_timeout_seconds,
            ) + bindings(module, payload)
        self._immutable()
        return Generated(payload, source, module)

    def verify(
        self, version: ProofVersion, payload: Certificate
    ) -> tuple[CacheManifest, dict[str, bytes]]:
        self._immutable()
        if version.environment_id != self.id:
            raise Invalid("Worker is not registered for the requested environment")
        data = self.settings.data_dir.resolve() / "checker"
        locks = data / "locks"
        locks.mkdir(parents=True, exist_ok=True)
        # Separate worker processes may check different curves, but never race on
        # the same deterministic Lean output path. No Lake builds are started.
        with (locks / (version.id + ".lock")).open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            checker = KernelChecker(
                self.environment,
                data,
                timeout=self.settings.check_timeout_seconds,
            )
            manifest = checker.check_payload(payload)
            source = next(
                a for a in manifest["artifacts"] if a["path"].endswith(".lean")
            )
            if source["sha256"] != version.source_sha256:
                raise Invalid("Reconstructed source differs from the frozen candidate")
            objects = {
                a["sha256"]: (
                    data / "objects" / a["sha256"][:2] / a["sha256"]
                ).read_bytes()
                for a in manifest["artifacts"]
            }
        manifest["validation_implementation"] = self.implementation
        self._immutable()
        return manifest, objects
