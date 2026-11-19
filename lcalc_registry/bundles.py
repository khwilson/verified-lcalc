"""Local, explicit checking of signed candidate bundles; no automatic publication."""

import base64
import hashlib
import json
import os
import re
import subprocess
import zipfile
from datetime import UTC, datetime
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from lcalc_registry.checker.contracts import JsonObject
from lcalc_registry.checker.environment import compatibility_manifest
from lcalc_registry.checker.kernel import audit
from lcalc_registry.checker.protocol import Invalid, canonical, certificate, digest

from .config import Settings
from .consumer import installed
from .proof_source import selection_source, usage_source


def check_bundle(
    path: Path, output: Path, public_key: Path, settings: Settings
) -> JsonObject:
    env = installed(settings)
    # The key authenticates the candidate source's origin, not its mathematical validity.
    key = serialization.load_pem_public_key(public_key.read_bytes())
    if not isinstance(key, Ed25519PublicKey):
        raise Invalid("Candidate bundles require a pinned Ed25519 public key")
    with zipfile.ZipFile(path) as z:
        names = z.namelist()
        if (
            len(names) != len(set(names))
            or len(names) > 5000
            or sum(i.file_size for i in z.infolist()) > 32 * 1024 * 1024
        ):
            raise Invalid("Bundle is oversized or has duplicate entries")
        reply = json.loads(z.read("bundle-attestation.json"))
        key.verify(
            base64.b64decode(reply["signature"], validate=True),
            canonical(reply["manifest"]),
        )
        manifest = reply["manifest"]
        if (
            manifest.get("schema") != "lcalc.candidate-bundle.v1"
            or manifest["environment_id"] != env.id
            or manifest["environment"] != env.public
        ):
            raise Invalid("Bundle does not match the installed exact Lean environment")
        if json.loads(z.read("manifest.json")) != manifest:
            raise Invalid("Bundle metadata differs from signed metadata")
        versions = manifest["versions"]
        if not 1 <= len(versions) <= 1000:
            raise Invalid("Invalid selection size")
        # Validate every source before writing or executing any of them.
        sources = []
        for v in versions:
            cid = v["candidate_id"]
            if not re.fullmatch("[0-9a-f]{64}", cid):
                raise Invalid("Invalid candidate ID")
            module = f"LcalcCertificates.C{cid}_E{env.id}"
            relative = module.replace(".", "/") + ".lean"
            if (
                v["module"] != module
                or v["path"] != relative
                or v["environment_id"] != env.id
            ):
                raise Invalid("Invalid proof module path")
            raw = z.read(relative)
            if hashlib.sha256(raw).hexdigest() != v["source_sha256"]:
                raise Invalid("Candidate source hash mismatch")
            witness = certificate(json.loads(z.read("witnesses/" + cid + ".json")))
            if digest(witness) != cid:
                raise Invalid("Witness hash mismatch")
            sources.append((v, raw, witness["rank"]))
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Remove a previous success report before checking this new selection.
    (output / "local-check.json").unlink(missing_ok=True)
    records = []
    for v, raw, _ in sources:
        source = output / v["path"]
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes(raw)
        prefix = source.with_suffix("")
        args = [
            str(env.lean),
            "-o",
            str(prefix.with_suffix(".olean")),
            "-i",
            str(prefix.with_suffix(".ilean")),
            "-c",
            str(prefix.with_suffix(".c")),
            v["path"],
        ]
        result = subprocess.run(
            args,
            cwd=output,
            env={
                **os.environ,
                "LEAN_PATH": str(output) + ":" + env.lean_path,
                "LEAN_NUM_THREADS": "1",
            },
            capture_output=True,
            text=True,
            timeout=settings.check_timeout_seconds,
        )
        log = result.stdout + result.stderr
        prefix.with_suffix(".validation.log").write_text(log)
        if result.returncode:
            raise Invalid("Lean rejected " + v["module"] + "; see local validation log")
        records.append(
            {
                "proof_version_id": v["id"],
                "source_sha256": v["source_sha256"],
                "axioms": audit(log, v["module"]),
            }
        )
    (output / "Selection.lean").write_text(
        selection_source([v["module"] for v, _, _ in sources])
    )
    (output / "Usage.lean").write_text(
        usage_source([(v["module"], rank) for v, _, rank in sources])
    )
    lean_path = str(output) + os.pathsep + env.lean_path
    # Compile consumers from imported objects. This also verifies the documented
    # reuse path, without repeating the numerical certificate proofs.
    for module in ["Selection", "Usage"]:
        result = subprocess.run(
            [str(env.lean), "-o", module + ".olean", module + ".lean"],
            cwd=output,
            env={**os.environ, "LEAN_PATH": lean_path, "LEAN_NUM_THREADS": "1"},
            capture_output=True,
            text=True,
            timeout=settings.check_timeout_seconds,
        )
        (output / (module + ".validation.log")).write_text(
            result.stdout + result.stderr
        )
        if result.returncode:
            raise Invalid(
                "Lean rejected bundle consumer " + module + "; see local validation log"
            )
    if compatibility_manifest(settings.checker_root, env.lean) != env.public:
        raise Invalid("Proof environment changed during local checking")
    report = {
        "schema": "lcalc.local-check.v1",
        "environment_id": env.id,
        "checked_at": datetime.now(UTC).isoformat(),
        "checks": records,
        "lean_path": lean_path,
        "import_module": "Usage",
        "trust": "Local kernel check; not an operator-signed registry verification event",
    }
    (output / "local-check.json").write_bytes(canonical(report))
    return report
