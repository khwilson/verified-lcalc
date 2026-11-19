"""Typed boundaries between candidate generation, kernel checking and persistence."""

from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Protocol, TypeAlias

from lcalc_registry.checker.contracts import (
    CacheManifest,
    Certificate,
    CurveSubject,
    EnvironmentManifest,
)

from .models import ProofVersion

CheckOutcome: TypeAlias = Literal["accepted", "rejected", "timeout"]


@dataclass(frozen=True)
class ProofEnvironment:
    id: str
    public: EnvironmentManifest
    lean: Path
    lean_path: str


@dataclass(frozen=True)
class Generated:
    witness: Certificate
    source: str
    module: str


class CheckingBackend(Protocol):
    @property
    def id(self) -> str: ...
    @property
    def manifest(self) -> Mapping[str, Any]: ...
    @property
    def implementation(self) -> dict[str, str]: ...
    def generate(self, subject: CurveSubject) -> Generated: ...
    def render(self, payload: Certificate) -> Generated: ...
    def verify(
        self, version: ProofVersion, payload: Certificate
    ) -> tuple[CacheManifest, dict[str, bytes]]: ...
