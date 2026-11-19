"""Shared SQLModel tables. Proof status is derived from immutable check records."""

from datetime import UTC, datetime
from uuid import uuid4

from sqlalchemy import (
    JSON,
    CheckConstraint,
    Column,
    DateTime,
    LargeBinary,
    Text,
    UniqueConstraint,
)
from sqlalchemy.dialects.postgresql import JSONB
from sqlmodel import Field, SQLModel

from lcalc_registry.checker.contracts import (
    Certificate,
    CurveSubject,
    JsonObject,
    RankStatement,
    SignedEnvelope,
)

Json = JSON().with_variant(JSONB(), "postgresql")


def now() -> datetime:
    return datetime.now(UTC)


def uid() -> str:
    return str(uuid4())


def json_column() -> Column[JsonObject]:
    return Column(Json, nullable=False)


class Source(SQLModel, table=True):
    __tablename__ = "registry_source"
    id: str = Field(primary_key=True, max_length=64)
    name: str = Field(max_length=200)
    provenance: JsonObject = Field(sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Curve(SQLModel, table=True):
    __tablename__ = "registry_curve"
    id: str = Field(primary_key=True, max_length=64)
    conductor: int = Field(index=True)
    subject: CurveSubject = Field(sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class SourceCurve(SQLModel, table=True):
    __tablename__ = "registry_source_curve"
    __table_args__ = (UniqueConstraint("source_id", "label"),)
    source_id: str = Field(foreign_key="registry_source.id", primary_key=True)
    curve_id: str = Field(foreign_key="registry_curve.id", primary_key=True)
    label: str = Field(primary_key=True, max_length=128, index=True)
    reference_claim: JsonObject = Field(default_factory=dict, sa_column=json_column())


class Environment(SQLModel, table=True):
    __tablename__ = "registry_environment"
    id: str = Field(primary_key=True, max_length=64)
    manifest: JsonObject = Field(sa_column=json_column())
    implementation: JsonObject = Field(sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Installation(SQLModel, table=True):
    __tablename__ = "registry_installation"
    id: str = Field(primary_key=True, max_length=64)
    environment_id: str = Field(foreign_key="registry_environment.id", index=True)
    implementation: JsonObject = Field(sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Artifact(SQLModel, table=True):
    __tablename__ = "registry_artifact"
    id: str = Field(primary_key=True, max_length=64)
    media_type: str
    size: int
    data: bytes = Field(sa_column=Column(LargeBinary, nullable=False))
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Candidate(SQLModel, table=True):
    __tablename__ = "registry_candidate"
    id: str = Field(primary_key=True, max_length=64)
    curve_id: str = Field(foreign_key="registry_curve.id", index=True)
    statement_id: str = Field(index=True)
    statement: RankStatement = Field(sa_column=json_column())
    witness: Certificate = Field(sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class ProofVersion(SQLModel, table=True):
    __tablename__ = "registry_proof_version"
    __table_args__ = (
        UniqueConstraint(
            "candidate_id", "environment_id", "source_sha256", "installation_id"
        ),
    )
    id: str = Field(primary_key=True, max_length=64)
    candidate_id: str = Field(foreign_key="registry_candidate.id", index=True)
    environment_id: str = Field(foreign_key="registry_environment.id", index=True)
    installation_id: str = Field(foreign_key="registry_installation.id")
    module: str
    source_sha256: str = Field(foreign_key="registry_artifact.id")
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Campaign(SQLModel, table=True):
    __tablename__ = "registry_campaign"
    id: str = Field(primary_key=True)
    name: str = Field(max_length=200)
    environment_id: str = Field(foreign_key="registry_environment.id")
    source_id: str | None = Field(default=None, foreign_key="registry_source.id")
    selection_sha256: str
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Task(SQLModel, table=True):
    __tablename__ = "registry_task"
    __table_args__ = (
        CheckConstraint("kind IN ('generate','verify')"),
        CheckConstraint(
            "status IN ('pending','running','succeeded','failed','inconclusive')"
        ),
    )
    id: str = Field(default_factory=uid, primary_key=True)
    installation_id: str = Field(foreign_key="registry_installation.id")
    kind: str
    status: str = Field(default="pending", index=True)
    environment_id: str = Field(foreign_key="registry_environment.id")
    curve_id: str | None = Field(default=None, foreign_key="registry_curve.id")
    proof_version_id: str | None = Field(
        default=None, foreign_key="registry_proof_version.id"
    )
    campaign_id: str | None = Field(
        default=None, foreign_key="registry_campaign.id", index=True
    )
    lease_token: str | None = None
    lease_until: datetime | None = Field(default=None, sa_type=DateTime(timezone=True))
    attempts: int = 0
    error: str | None = Field(default=None, sa_column=Column(Text))
    result: JsonObject = Field(default_factory=dict, sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class CampaignMember(SQLModel, table=True):
    __tablename__ = "registry_campaign_member"
    campaign_id: str = Field(foreign_key="registry_campaign.id", primary_key=True)
    proof_version_id: str = Field(
        foreign_key="registry_proof_version.id", primary_key=True
    )
    task_id: str = Field(foreign_key="registry_task.id", unique=True)


class Verification(SQLModel, table=True):
    __tablename__ = "registry_verification"
    __table_args__ = (
        UniqueConstraint("task_id"),
        CheckConstraint("outcome IN ('accepted','rejected','timeout')"),
    )
    id: str = Field(default_factory=uid, primary_key=True)
    task_id: str = Field(foreign_key="registry_task.id")
    proof_version_id: str = Field(foreign_key="registry_proof_version.id", index=True)
    environment_id: str = Field(foreign_key="registry_environment.id", index=True)
    installation_id: str = Field(foreign_key="registry_installation.id")
    outcome: str
    checked_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))
    envelope: SignedEnvelope[JsonObject] = Field(sa_column=json_column())
    error: str | None = Field(default=None, sa_column=Column(Text))


class CampaignReport(SQLModel, table=True):
    __tablename__ = "registry_campaign_report"
    campaign_id: str = Field(foreign_key="registry_campaign.id", primary_key=True)
    id: str = Field(unique=True)
    envelope: SignedEnvelope[JsonObject] = Field(sa_column=json_column())
    created_at: datetime = Field(default_factory=now, sa_type=DateTime(timezone=True))


class Schedule(SQLModel, table=True):
    __tablename__ = "registry_schedule"
    __table_args__ = (CheckConstraint("interval_seconds >= 60"),)
    id: str = Field(default_factory=uid, primary_key=True)
    name: str
    source_id: str = Field(foreign_key="registry_source.id")
    environment_id: str = Field(foreign_key="registry_environment.id")
    interval_seconds: int
    next_due: datetime = Field(sa_type=DateTime(timezone=True))
    limit: int = 100
    enabled: bool = True
