"""Fetch signed proof artifacts without re-running numerical checks."""

import base64
import hashlib
import json
import re
import tempfile
import urllib.parse
import urllib.request
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Any

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from .checker.contracts import CachedProof
from .checker.protocol import Invalid, canonical, digest


class RegistryCache:
    def __init__(
        self,
        url: str,
        key: Path,
        directory: Path,
        environment: Mapping[str, Any],
        get: Callable[[str], bytes] | None = None,
    ) -> None:
        address = urllib.parse.urlsplit(url)
        if (
            address.username
            or address.password
            or address.query
            or address.fragment
            or not address.hostname
            or not (
                address.scheme == "https"
                or (
                    address.scheme == "http"
                    and address.hostname in ["127.0.0.1", "localhost"]
                )
            )
        ):
            raise Invalid("Use HTTPS for a remote cache")
        self.url = url.rstrip("/")
        self.key = Path(key)
        self.directory = Path(directory).resolve()
        self.environment = environment
        self.get = get or self.download

    def download(self, path: str) -> bytes:
        with urllib.request.urlopen(self.url + path, timeout=30) as reply:
            data = reply.read(64 * 1024 * 1024 + 1)
        if len(data) > 64 * 1024 * 1024:
            raise Invalid("Cache object exceeds download limit")
        return data

    def verify_signature(self, data: Path, signature: str) -> None:
        try:
            key = serialization.load_pem_public_key(self.key.read_bytes())
            if not isinstance(key, Ed25519PublicKey):
                raise Invalid("Cache requires a pinned Ed25519 public key")
            key.verify(base64.b64decode(signature, validate=True), data.read_bytes())
        except Exception as error:
            raise Invalid(
                "Manifest signature does not match the pinned public key"
            ) from error

    def fetch(self, certificate_id: str) -> CachedProof:
        if not re.fullmatch("[0-9a-f]{64}", certificate_id):
            raise Invalid("Invalid certificate identifier")
        eid = digest(self.environment)
        reply = json.loads(
            self.get("/v1/certificates/" + certificate_id + "?environment=" + eid)
        )
        if set(reply) != {"manifest", "signature"}:
            raise Invalid("Invalid manifest envelope")
        manifest = reply["manifest"]
        with tempfile.TemporaryDirectory() as tmp:
            data = Path(tmp) / "manifest.json"
            data.write_bytes(canonical(manifest))
            self.verify_signature(data, reply["signature"])
            if (
                manifest["schema"] != "lcalc.cache-manifest.v1"
                or manifest["certificate_id"] != certificate_id
                or manifest["environment_id"] != eid
                or manifest["environment"] != self.environment
            ):
                raise Invalid("Certificate or environment mismatch")
            module = manifest["module"]
            expected = "LcalcCertificates.C" + certificate_id + "_E" + eid
            if module != expected:
                raise Invalid("Unexpected theorem module")
            target = self.directory / eid
            staging = Path(tmp) / "staging"
            seen = set()
            for item in manifest["artifacts"]:
                path = Path(item["path"])
                if (
                    path.is_absolute()
                    or ".." in path.parts
                    or str(path) in seen
                    or path.parent != Path("LcalcCertificates")
                ):
                    raise Invalid("Invalid artifact path")
                if not str(path.name).startswith(module.split(".")[-1] + "."):
                    raise Invalid("Artifact belongs to another module")
                if (
                    not re.fullmatch("[0-9a-f]{64}", item["sha256"])
                    or not isinstance(item["size"], int)
                    or not 0 <= item["size"] <= 64 * 1024 * 1024
                ):
                    raise Invalid("Invalid artifact metadata")
                suffix = str(path.name)[len(module.split(".")[-1]) :]
                if suffix not in [
                    ".lean",
                    ".olean",
                    ".olean.private",
                    ".olean.server",
                    ".ir",
                    ".ir.sig",
                    ".ilean",
                ]:
                    raise Invalid("Unexpected artifact type")
                seen.add(str(path))
                raw = self.get("/v1/objects/" + item["sha256"])
                if (
                    len(raw) != item["size"]
                    or hashlib.sha256(raw).hexdigest() != item["sha256"]
                ):
                    raise Invalid("Artifact integrity check failed")
                output = staging / path
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(raw)
            if module.replace(".", "/") + ".olean" not in seen:
                raise Invalid("Cache has no compiled theorem")
            target.mkdir(parents=True, exist_ok=True)
            for path in staging.rglob("*"):
                if path.is_file():
                    output = target / path.relative_to(staging)
                    output.parent.mkdir(parents=True, exist_ok=True)
                    if output.exists() and output.read_bytes() != path.read_bytes():
                        raise Invalid("Conflicting immutable artifact already cached")
            for path in staging.rglob("*"):
                if path.is_file():
                    output = target / path.relative_to(staging)
                    temp = output.with_suffix(output.suffix + ".tmp")
                    temp.write_bytes(path.read_bytes())
                    temp.replace(output)
            (target / (certificate_id + ".manifest.json")).write_bytes(canonical(reply))
        return {
            "module": module,
            "lean_path": str(target),
            "certificate_id": certificate_id,
            "environment_id": eid,
        }
