"""Wire contracts for exact Lean witnesses and signed compiled-proof manifests.

Decimal and rational strings stay strings; these types do not assert their
mathematical validity. protocol.py validates their wire format and Lean checks
mathematical correctness.
"""

from typing import Any, Generic, Literal, TypeAlias, TypeVar

from typing_extensions import TypedDict

JsonObject: TypeAlias = dict[str, Any]
Rank: TypeAlias = Literal["0", "1"]
AxiomAudit: TypeAlias = dict[str, list[str]]


class CurveSubject(TypedDict):
    ainvs: list[str]
    conductor: str


class Parameters(TypedDict):
    precision_bits: str
    terms: str
    steps_per_unit: str
    cutoff: str


class TateWitness(TypedDict):
    r: str
    s: str
    t: str
    starT: str
    cubicRoot: str
    quadraticRoot: str
    chain: list[str]
    kodaira: str


class ArithmeticWitness(TypedDict):
    minimality: list[str]
    at_two: TateWitness | None
    at_three: TateWitness | None


class Enclosure(TypedDict):
    real: list[str]
    imag: list[str]


class CentralEvaluator(TypedDict):
    alpha: list[str]
    tail: str
    geometric_upper: str


class DerivativeEvaluator(TypedDict):
    alpha: list[str]
    tail: str
    finite: list[str]


class CertificateFields(TypedDict):
    schema: Literal["lcalc.ec-rank.v1"]
    subject: CurveSubject
    parameters: Parameters
    coefficients: list[str]
    arithmetic: ArithmeticWitness
    enclosure: Enclosure


class CentralCertificate(CertificateFields):
    rank: Literal["0"]
    evaluator: CentralEvaluator


class DerivativeCertificate(CertificateFields):
    rank: Literal["1"]
    evaluator: DerivativeEvaluator


Certificate: TypeAlias = CentralCertificate | DerivativeCertificate


class RankStatement(TypedDict):
    schema: Literal["lcalc.ec-rank-statement.v1"]
    subject: CurveSubject
    normalization: Literal["elliptic-hasse-weil-L"]
    center: Literal["1"]
    analytic_rank: Rank


class ArtifactMetadata(TypedDict):
    path: str
    sha256: str
    size: int


class EnvironmentManifest(TypedDict):
    schema: Literal["lcalc.environment.v1"]
    lean: str
    mathlib: str
    tau_ceti: str | None
    platform: dict[str, str | int]
    checker_sources: dict[str, str]
    modularity_statement_sha256: str


class CacheManifest(TypedDict):
    schema: Literal["lcalc.cache-manifest.v1"]
    certificate_id: str
    statement_id: str
    statement: RankStatement
    environment_id: str
    environment: EnvironmentManifest
    module: str
    axioms: AxiomAudit
    artifacts: list[ArtifactMetadata]
    validation_implementation: dict[str, str]
    validated_at: float
    validation_seconds: float
    trust: str


Manifest = TypeVar("Manifest")


class SignedEnvelope(TypedDict, Generic[Manifest]):
    manifest: Manifest
    signature: str


class CachedProof(TypedDict):
    module: str
    lean_path: str
    certificate_id: str
    environment_id: str
