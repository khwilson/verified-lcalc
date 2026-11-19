"""Attestations identify this operator; they are not cryptographic proofs of execution."""

import base64
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from lcalc_registry.checker.contracts import Manifest, SignedEnvelope
from lcalc_registry.checker.protocol import canonical


class Signer:
    def __init__(self, directory: Path) -> None:
        self.directory = directory

    def initialize(self) -> None:
        self.directory.mkdir(parents=True, exist_ok=True)
        path = self.directory / "signing-private.pem"
        if not path.exists():
            key = Ed25519PrivateKey.generate()
            # Never overwrite an existing key or print its contents.
            with path.open("xb") as f:
                path.chmod(0o600)
                f.write(
                    key.private_bytes(
                        serialization.Encoding.PEM,
                        serialization.PrivateFormat.PKCS8,
                        serialization.NoEncryption(),
                    )
                )
        key = self._key()
        public = self.directory / "signing-public.pem"
        public.write_bytes(
            key.public_key().public_bytes(
                serialization.Encoding.PEM,
                serialization.PublicFormat.SubjectPublicKeyInfo,
            )
        )

    def _key(self) -> Ed25519PrivateKey:
        key = serialization.load_pem_private_key(
            (self.directory / "signing-private.pem").read_bytes(), password=None
        )
        if not isinstance(key, Ed25519PrivateKey):
            raise ValueError("The registry requires an Ed25519 signing key")
        return key

    def public_key(self) -> bytes:
        return (
            self._key()
            .public_key()
            .public_bytes(
                serialization.Encoding.PEM,
                serialization.PublicFormat.SubjectPublicKeyInfo,
            )
        )

    def envelope(self, manifest: Manifest) -> SignedEnvelope[Manifest]:
        return {
            "manifest": manifest,
            "signature": base64.b64encode(
                self._key().sign(canonical(manifest))
            ).decode(),
        }
