"""One application service shared by HTTP, MCP and CLI; no mathematical algorithms."""

import hashlib
import io
import json
import secrets
import zipfile
from collections.abc import Mapping, Sequence
from datetime import UTC, datetime, timedelta
from typing import Any, TypedDict, TypeVar, cast

from sqlalchemy import case, func, or_, text
from sqlalchemy.engine import Engine
from sqlmodel import Session, SQLModel, col, select

from lcalc_registry.checker.contracts import (
    CacheManifest,
    Certificate,
    CurveSubject,
    JsonObject,
    SignedEnvelope,
)
from lcalc_registry.checker.protocol import (
    Invalid,
    canonical,
    certificate,
    digest,
    integer,
    statement,
    subject,
)

from .contracts import CheckOutcome
from .models import (
    Artifact,
    Campaign,
    CampaignMember,
    CampaignReport,
    Candidate,
    Curve,
    Environment,
    Installation,
    ProofVersion,
    Schedule,
    Source,
    SourceCurve,
    Task,
    Verification,
    now,
    uid,
)
from .proof_source import selection_source, usage_source
from .signing import Signer

Model = TypeVar("Model", bound=SQLModel)


class SourceRow(TypedDict):
    label: str
    subject: CurveSubject
    reference_claim: dict[str, str]


class QueueFull(Exception):
    pass


class Missing(LookupError):
    pass


def required(session: Session, model: type[Model], key: str | tuple[Any, ...]) -> Model:
    value = session.get(model, key)
    if value is None:
        raise Missing(f"{model.__name__} {key} not found")
    return value


def utc(value: datetime) -> datetime:
    return value.replace(tzinfo=UTC) if value.tzinfo is None else value


def insert_once(session: Session, model: type[Model], **values: Any) -> Model:
    """Insert immutable rows without UPDATE, including concurrent duplicate generation."""
    from sqlalchemy.dialects.postgresql import insert as pg_insert
    from sqlalchemy.dialects.sqlite import insert as sqlite_insert

    insert = (
        pg_insert if session.get_bind().dialect.name == "postgresql" else sqlite_insert
    )
    row = model(**values)
    session.exec(insert(model).values(**row.model_dump()).on_conflict_do_nothing())
    from sqlalchemy import inspect

    mapper = inspect(model)
    if mapper is None:
        raise TypeError("Expected a mapped SQLModel table")
    primary = tuple(values[c.key] for c in mapper.primary_key)
    return required(session, model, primary[0] if len(primary) == 1 else primary)


def installation_id(environment_id: str, implementation: dict[str, str]) -> str:
    return digest({"environment_id": environment_id, "implementation": implementation})


def artifact(session: Session, data: bytes, media_type: str) -> Artifact:
    key = hashlib.sha256(data).hexdigest()
    value = insert_once(
        session, Artifact, id=key, data=data, size=len(data), media_type=media_type
    )
    if value.size != len(data) or value.data != data:
        raise Invalid("Stored artifact failed its content address")
    return value


class Registry:
    def __init__(self, engine: Engine, signer: Signer) -> None:
        self.engine = engine
        self.signer = signer

    def register_environment(
        self, manifest: Mapping[str, Any], implementation: dict[str, str]
    ) -> Environment:
        key = digest(manifest)
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            value = insert_once(
                s, Environment, id=key, manifest=manifest, implementation=implementation
            )
            if value.manifest != manifest:
                raise Invalid("Environment identity mismatch")
            insert_once(
                s,
                Installation,
                id=installation_id(key, implementation),
                environment_id=key,
                implementation=implementation,
            )

        return value

    def import_source(
        self, name: str, rows: list[JsonObject], provenance: JsonObject
    ) -> Source:
        if not name or len(name) > 200 or not 1 <= len(rows) <= 10000:
            raise Invalid("Provide a source name and 1–10000 input rows")
        try:
            json.dumps(provenance, allow_nan=False)
        except (ValueError, TypeError) as error:
            raise Invalid("Provenance must contain finite JSON values") from error
        clean: list[SourceRow] = []
        labels = set()
        for row in rows:
            if (
                not isinstance(row, dict)
                or not {"label", "ainvs", "conductor"} <= set(row)
                or not isinstance(row["ainvs"], list)
            ):
                raise Invalid("Each row must provide label, five ainvs, and conductor")
            label = row.get("label")
            if (
                not isinstance(label, str)
                or not 1 <= len(label) <= 128
                or label in labels
            ):
                raise Invalid("Labels must be unique nonempty strings in a snapshot")
            labels.add(label)
            # Expected ranks are external claims on SourceCurve; only subject goes to generation.
            data = subject(
                {
                    "ainvs": [str(x) for x in row["ainvs"]],
                    "conductor": str(row["conductor"]),
                }
            )
            reference = {}
            if row.get("analytic_rank") is not None:
                reference["analytic_rank"] = integer(str(row["analytic_rank"]), False)
            clean.append(
                {"label": label, "subject": data, "reference_claim": reference}
            )
        clean.sort(key=lambda x: x["label"])
        key = digest(
            {
                "schema": "lcalc.source.v1",
                "name": name,
                "inputs": clean,
                "provenance": provenance,
            }
        )
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            old = s.get(Source, key)
            if old:
                return old
            value = insert_once(s, Source, id=key, name=name, provenance=provenance)
            for row in clean:
                cid = digest(row["subject"])
                if s.get(Curve, cid) is None:
                    insert_once(
                        s,
                        Curve,
                        id=cid,
                        conductor=int(row["subject"]["conductor"]),
                        subject=row["subject"],
                    )
                from sqlalchemy.dialects.postgresql import insert as pg_insert
                from sqlalchemy.dialects.sqlite import insert as sqlite_insert

                insert = (
                    pg_insert
                    if self.engine.dialect.name == "postgresql"
                    else sqlite_insert
                )
                s.exec(
                    insert(SourceCurve)
                    .values(
                        source_id=key,
                        curve_id=cid,
                        label=row["label"],
                        reference_claim=row["reference_claim"],
                    )
                    .on_conflict_do_nothing()
                )
        return value

    def get(self, model: type[Model], key: str) -> Model:
        with Session(self.engine, expire_on_commit=False) as s:
            return required(s, model, key)

    def sources(self) -> Sequence[Source]:
        with Session(self.engine, expire_on_commit=False) as s:
            return s.exec(
                select(Source).order_by(col(Source.created_at).desc()).limit(100)
            ).all()

    def environments(self) -> Sequence[Environment]:
        with Session(self.engine, expire_on_commit=False) as s:
            return s.exec(
                select(Environment).order_by(col(Environment.created_at).desc())
            ).all()

    def curves(
        self,
        source_id: str | None = None,
        conductor: int | None = None,
        label: str | None = None,
        limit: int = 100,
        offset: int = 0,
    ) -> list[JsonObject]:
        if not 1 <= limit <= 1000 or offset < 0:
            raise Invalid("Invalid page size or offset")
        query = select(
            Curve,
            col(SourceCurve.label),
            col(SourceCurve.source_id),
            col(SourceCurve.reference_claim),
        ).join(SourceCurve, col(SourceCurve.curve_id) == col(Curve.id))
        if source_id:
            query = query.where(col(SourceCurve.source_id) == source_id)
        if conductor is not None:
            query = query.where(col(Curve.conductor) == conductor)
        if label:
            query = query.where(col(SourceCurve.label) == label)
        with Session(self.engine, expire_on_commit=False) as s:
            return [
                {
                    **c.model_dump(),
                    "label": lab,
                    "source_id": src,
                    "reference_claim": ref,
                }
                for c, lab, src, ref in s.exec(
                    query.order_by(col(Curve.conductor), col(SourceCurve.label))
                    .offset(offset)
                    .limit(limit)
                )
            ]

    def enqueue_generation(
        self, curve_ids: Sequence[str], environment_id: str
    ) -> list[Task]:
        keys = list(dict.fromkeys(curve_ids))
        if not 1 <= len(keys) <= 1000:
            raise Invalid("Select 1–1000 curves")
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            required(s, Environment, environment_id)
            installation = s.exec(
                select(Installation)
                .where(col(Installation.environment_id) == environment_id)
                .order_by(col(Installation.created_at).desc())
                .limit(1)
            ).one()
            result = []
            for cid in keys:
                required(s, Curve, cid)
                task = Task(
                    kind="generate",
                    curve_id=cid,
                    environment_id=environment_id,
                    installation_id=installation.id,
                )
                s.add(task)
                result.append(task)
        return result

    def request_proof(
        self,
        source_id: str,
        label: str,
        environment_id: str,
        witness: object = None,
        *,
        max_pending: int = 64,
    ) -> Task:
        """Idempotently queue source generation for a known snapshot curve.

        Submitted JSON is frozen as a content-addressed artifact. No submitted
        Lean source is accepted, and this operation never queues kernel work.
        """
        payload = certificate(witness) if witness is not None else None
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            if self.engine.dialect.name == "postgresql":
                s.connection().execute(text("SELECT pg_advisory_xact_lock(824630192)"))
            else:
                s.connection().execute(text("BEGIN IMMEDIATE"))
            required(s, Source, source_id)
            row = s.exec(
                select(SourceCurve).where(
                    col(SourceCurve.source_id) == source_id,
                    col(SourceCurve.label) == label,
                )
            ).one_or_none()
            if row is None:
                raise Missing("Curve label not found in this source snapshot")
            curve = required(s, Curve, row.curve_id)
            required(s, Environment, environment_id)
            installation = s.exec(
                select(Installation)
                .where(col(Installation.environment_id) == environment_id)
                .order_by(col(Installation.created_at).desc())
                .limit(1)
            ).one()
            if payload is not None and payload["subject"] != curve.subject:
                raise Invalid("Submitted witness does not match the snapshot curve")
            request = {
                "source_id": source_id,
                "label": label,
                "environment_id": environment_id,
                "installation_id": installation.id,
                "witness_sha256": digest(payload) if payload is not None else None,
            }
            key = "proof-request-" + digest(request)
            existing = s.get(Task, key)
            if existing is not None:
                return existing
            pending = s.exec(
                select(func.count())
                .select_from(Task)
                .where(col(Task.status).in_(["pending", "running"]))
            ).one()
            if pending >= max_pending:
                raise QueueFull("Proof generation queue is full; try again later")
            if payload is not None:
                obj = artifact(s, canonical(payload), "application/json")
                if obj.id != request["witness_sha256"]:
                    raise Invalid("Witness content address mismatch")
            task = Task(
                id=key,
                kind="generate",
                curve_id=curve.id,
                environment_id=environment_id,
                installation_id=installation.id,
                result={"request": request},
            )
            s.add(task)
        return task

    def submitted_witness(self, task: Task) -> Certificate | None:
        request = task.result.get("request", {})
        sha = request.get("witness_sha256")
        if sha is None:
            return None
        raw = self.get(Artifact, sha).data
        payload = certificate(json.loads(raw))
        if digest(payload) != sha or digest(payload["subject"]) != task.curve_id:
            raise Invalid("Frozen submitted witness failed its content address")
        return payload

    def versions(
        self,
        curve_id: str | None = None,
        environment_id: str | None = None,
        source_id: str | None = None,
        limit: int = 100,
        offset: int = 0,
    ) -> list[JsonObject]:
        if not 1 <= limit <= 1000 or offset < 0:
            raise Invalid("Invalid page size or offset")
        query = select(ProofVersion, Candidate).join(
            Candidate, col(Candidate.id) == col(ProofVersion.candidate_id)
        )
        if curve_id:
            query = query.where(col(Candidate.curve_id) == curve_id)
        if environment_id:
            query = query.where(col(ProofVersion.environment_id) == environment_id)
        if source_id:
            query = query.where(
                col(Candidate.curve_id).in_(
                    select(col(SourceCurve.curve_id)).where(
                        col(SourceCurve.source_id) == source_id
                    )
                )
            )
        with Session(self.engine, expire_on_commit=False) as s:
            values = s.exec(
                query.order_by(
                    col(ProofVersion.created_at).desc(), col(ProofVersion.id)
                )
                .offset(offset)
                .limit(limit)
            ).all()
            output = []
            for version, candidate in values:
                latest = s.exec(
                    select(Verification)
                    .where(col(Verification.proof_version_id) == version.id)
                    .order_by(col(Verification.checked_at).desc())
                    .limit(1)
                ).first()
                accepted = s.exec(
                    select(Verification)
                    .where(
                        col(Verification.proof_version_id) == version.id,
                        col(Verification.outcome) == "accepted",
                    )
                    .order_by(col(Verification.checked_at).desc())
                    .limit(1)
                ).first()
                active_check = s.exec(
                    select(Task)
                    .where(
                        col(Task.proof_version_id) == version.id,
                        col(Task.kind) == "verify",
                        col(Task.status).in_(["pending", "running"]),
                    )
                    .order_by(
                        case((col(Task.status) == "running", 0), else_=1),
                        col(Task.created_at),
                        col(Task.id),
                    )
                    .limit(1)
                ).first()
                verification_status = (
                    ("running" if active_check.status == "running" else "queued")
                    if active_check
                    else latest.outcome
                    if latest
                    else "not_requested"
                )
                output.append(
                    {
                        **version.model_dump(),
                        "curve_id": candidate.curve_id,
                        "statement": candidate.statement,
                        "status": verification_status
                        if active_check
                        else "checked"
                        if accepted
                        else "candidate",
                        "verification_status": verification_status,
                        "verification_task": active_check.model_dump(
                            exclude={"lease_token"}
                        )
                        if active_check
                        else None,
                        "last_check": latest.model_dump() if latest else None,
                        "last_accepted_check": accepted.model_dump()
                        if accepted
                        else None,
                    }
                )
            return output

    def register_candidate(
        self, task_id: str, token: str, payload: Certificate, source: str, module: str
    ) -> str:
        certificate(payload)
        cid = digest(payload)
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            task = self._owned(s, task_id, token)
            if task.kind != "generate" or digest(payload["subject"]) != task.curve_id:
                raise Invalid("Generated witness does not match task")
            submitted_sha = task.result.get("request", {}).get("witness_sha256")
            if submitted_sha is not None and submitted_sha != cid:
                raise Invalid("Renderer changed the frozen submitted witness")
            expected = f"LcalcCertificates.C{cid}_E{task.environment_id}"
            if module != expected:
                raise Invalid(
                    "Generated module is not bound to the candidate and environment"
                )
            if s.get(Candidate, cid) is None:
                insert_once(
                    s,
                    Candidate,
                    id=cid,
                    curve_id=task.curve_id,
                    witness=payload,
                    statement=statement(payload),
                    statement_id=digest(statement(payload)),
                )
            obj = artifact(s, source.encode(), "text/plain; charset=utf-8")
            vid = digest(
                {
                    "candidate": cid,
                    "environment": task.environment_id,
                    "source": obj.id,
                    "installation": task.installation_id,
                }
            )
            version = s.get(ProofVersion, vid)
            if version is None:
                version = insert_once(
                    s,
                    ProofVersion,
                    id=vid,
                    candidate_id=cid,
                    environment_id=task.environment_id,
                    installation_id=task.installation_id,
                    module=module,
                    source_sha256=obj.id,
                )
            task.status = "succeeded"
            task.result = {
                **task.result,
                "proof_version_id": vid,
                "candidate_id": cid,
                "status": "candidate",
            }
            task.lease_token = None
            task.lease_until = None
            s.add(task)
        return vid

    def create_campaign(
        self,
        name: str,
        version_ids: Sequence[str],
        campaign_id: str | None = None,
        session: Session | None = None,
        source_id: str | None = None,
    ) -> Campaign:
        keys = sorted(set(version_ids))
        if not 1 <= len(keys) <= 1000 or not name or len(name) > 200:
            raise Invalid("Select 1–1000 proof versions and a campaign name")

        def create(s: Session) -> Campaign:
            key = campaign_id or uid()
            old = s.get(Campaign, key)
            if old:
                return old
            versions = [required(s, ProofVersion, v) for v in keys]
            if source_id is not None:
                required(s, Source, source_id)
                available = set(
                    s.exec(
                        select(col(SourceCurve.curve_id)).where(
                            col(SourceCurve.source_id) == source_id
                        )
                    ).all()
                )
                if any(
                    required(s, Candidate, v.candidate_id).curve_id not in available
                    for v in versions
                ):
                    raise Invalid(
                        "Campaign includes a curve outside the frozen source snapshot"
                    )
            environments = {v.environment_id for v in versions}
            if len(environments) != 1:
                raise Invalid("A campaign must use one exact environment")
            campaign = Campaign(
                id=key,
                name=name,
                environment_id=versions[0].environment_id,
                source_id=source_id,
                selection_sha256=digest(keys),
            )
            s.add(campaign)
            s.flush()
            for version in versions:
                task = Task(
                    kind="verify",
                    proof_version_id=version.id,
                    environment_id=version.environment_id,
                    installation_id=version.installation_id,
                    campaign_id=key,
                )
                s.add(task)
                s.flush()
                s.add(
                    CampaignMember(
                        campaign_id=key, proof_version_id=version.id, task_id=task.id
                    )
                )
            return campaign

        if session is not None:
            return create(session)
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            result = create(s)
        return result

    def claim(
        self,
        environment_id: str,
        lease_seconds: int,
        implementation_id: str | None = None,
    ) -> Task | None:
        timestamp = now()
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            query = (
                select(Task)
                .where(
                    col(Task.environment_id) == environment_id,
                    or_(
                        col(Task.status) == "pending",
                        (col(Task.status) == "running")
                        & (col(Task.lease_until) < timestamp),
                    ),
                )
                .order_by(col(Task.created_at), col(Task.id))
                .with_for_update(skip_locked=True)
                .limit(1)
            )
            if implementation_id is not None:
                query = query.where(col(Task.installation_id) == implementation_id)
            task = s.exec(query).first()
            if task is None:
                return None
            task.status = "running"
            task.attempts += 1
            task.lease_token = secrets.token_hex(32)
            task.lease_until = timestamp + timedelta(seconds=lease_seconds)
            s.add(task)
        return task

    def _owned(self, s: Session, task_id: str, token: str) -> Task:
        task = s.exec(
            select(Task).where(col(Task.id) == task_id).with_for_update()
        ).first()
        if (
            task is None
            or task.status != "running"
            or not secrets.compare_digest(task.lease_token or "", token)
            or task.lease_until is None
            or utc(task.lease_until) <= now()
        ):
            raise Invalid(
                "Task lease expired or was superseded; result cannot be published"
            )
        return task

    def fail_task(
        self, task_id: str, token: str, message: str, inconclusive: bool = False
    ) -> None:
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            task = self._owned(s, task_id, token)
            task.status = "inconclusive" if inconclusive else "failed"
            task.error = message[:2000]
            task.lease_token = None
            task.lease_until = None
            s.add(task)

    def record_check(
        self,
        task_id: str,
        token: str,
        outcome: CheckOutcome,
        manifest: CacheManifest | None = None,
        objects: dict[str, bytes] | None = None,
        error: str | None = None,
    ) -> Verification:
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            task = self._owned(s, task_id, token)
            if task.kind != "verify":
                raise Invalid(
                    "Only verification tasks may publish verification records"
                )
            if task.proof_version_id is None:
                raise Invalid("Verification task has no proof version")
            version = required(s, ProofVersion, task.proof_version_id)
            if outcome not in ["accepted", "rejected", "timeout"]:
                raise Invalid("Invalid verification outcome")
            # This method is called only by the operator's checker, never exposed as CRUD.
            if outcome == "accepted":
                if manifest is None or objects is None:
                    raise Invalid(
                        "Accepted checks require a manifest and all artifact bytes"
                    )
                if (
                    manifest["certificate_id"] != version.candidate_id
                    or manifest["environment_id"] != version.environment_id
                    or manifest["module"] != version.module
                ):
                    raise Invalid(
                        "Checked manifest does not match requested proof version"
                    )
                if (
                    manifest["environment"]
                    != required(s, Environment, version.environment_id).manifest
                ):
                    raise Invalid(
                        "Manifest dependencies differ from the registered profile"
                    )
                if (
                    manifest.get("validation_implementation")
                    != required(s, Installation, task.installation_id).implementation
                ):
                    raise Invalid(
                        "Manifest checker implementation differs from the assigned installation"
                    )
                expected = {v["sha256"] for v in manifest["artifacts"]}
                if set(objects or {}) != expected:
                    raise Invalid("Checked artifact set is incomplete")
                if not any(
                    v["path"] == version.module.replace(".", "/") + ".lean"
                    and v["sha256"] == version.source_sha256
                    for v in manifest["artifacts"]
                ):
                    raise Invalid(
                        "Checked source differs from the frozen candidate source"
                    )
                for key, raw in objects.items():
                    if hashlib.sha256(raw).hexdigest() != key:
                        raise Invalid("Checked artifact digest mismatch")
                    artifact(s, raw, "application/octet-stream")
                envelope = self.signer.envelope(manifest)
            else:
                envelope = self.signer.envelope(
                    {
                        "schema": "lcalc.failed-check.v1",
                        "proof_version_id": version.id,
                        "environment_id": version.environment_id,
                        "outcome": outcome,
                        "checked_at": now().isoformat(),
                        "error": error,
                    }
                )
            check = Verification(
                task_id=task.id,
                proof_version_id=version.id,
                environment_id=version.environment_id,
                installation_id=task.installation_id,
                outcome=outcome,
                envelope=envelope,
                error=error,
            )
            s.add(check)
            task.status = "succeeded" if outcome == "accepted" else "failed"
            task.result = {"verification_id": check.id, "outcome": outcome}
            task.error = error
            task.lease_token = None
            task.lease_until = None
            s.add(task)
        return check

    def checks(
        self, version_id: str | None = None, limit: int = 100
    ) -> Sequence[Verification]:
        query = select(Verification)
        if version_id:
            query = query.where(col(Verification.proof_version_id) == version_id)
        with Session(self.engine, expire_on_commit=False) as s:
            return s.exec(
                query.order_by(col(Verification.checked_at).desc()).limit(
                    min(max(limit, 1), 1000)
                )
            ).all()

    def campaign_status(self, key: str) -> JsonObject:
        with Session(self.engine, expire_on_commit=False) as s:
            campaign = required(s, Campaign, key)
            rows = s.exec(
                select(CampaignMember, Task)
                .join(Task, col(Task.id) == col(CampaignMember.task_id))
                .where(col(CampaignMember.campaign_id) == key)
                .order_by(col(CampaignMember.proof_version_id))
            ).all()
            members = []
            for member, task in rows:
                check = s.exec(
                    select(Verification).where(col(Verification.task_id) == task.id)
                ).first()
                comparisons = []
                if campaign.source_id and check and check.outcome == "accepted":
                    version = required(s, ProofVersion, member.proof_version_id)
                    candidate = required(s, Candidate, version.candidate_id)
                    for reference in s.exec(
                        select(SourceCurve).where(
                            col(SourceCurve.source_id) == campaign.source_id,
                            col(SourceCurve.curve_id) == candidate.curve_id,
                        )
                    ):
                        if "analytic_rank" in reference.reference_claim:
                            expected = reference.reference_claim["analytic_rank"]
                            comparisons.append(
                                {
                                    "label": reference.label,
                                    "reference_analytic_rank": expected,
                                    "proved_analytic_rank": candidate.statement[
                                        "analytic_rank"
                                    ],
                                    "matches": expected
                                    == candidate.statement["analytic_rank"],
                                }
                            )
                members.append(
                    {
                        "proof_version_id": member.proof_version_id,
                        "task_id": task.id,
                        "status": task.status,
                        "verification_id": check.id if check else None,
                        "outcome": check.outcome if check else None,
                        "reference_comparisons": comparisons,
                    }
                )
            return {
                **campaign.model_dump(mode="json"),
                "members": members,
                "complete": bool(members)
                and all(
                    x["status"] in ["succeeded", "failed", "inconclusive"]
                    for x in members
                ),
            }

    def seal_campaign(self, key: str) -> CampaignReport | None:
        status = self.campaign_status(key)
        if not status["complete"]:
            return None
        report = {
            "schema": "lcalc.campaign-report.v1",
            **status,
            "recorded_at": now().isoformat(),
            "accepted": sum(m["outcome"] == "accepted" for m in status["members"]),
            "reference_mismatches": sum(
                not c["matches"]
                for m in status["members"]
                for c in m["reference_comparisons"]
            ),
        }
        envelope = self.signer.envelope(report)
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            old = s.get(CampaignReport, key)
            if old:
                return old
            value = insert_once(
                s, CampaignReport, campaign_id=key, id=digest(report), envelope=envelope
            )
        return value

    def proof_bundle(self, version_ids: Sequence[str]) -> bytes:
        keys = sorted(set(version_ids))
        if not 1 <= len(keys) <= 1000:
            raise Invalid("Select 1–1000 proof versions")
        with Session(self.engine, expire_on_commit=False) as s:
            versions = [required(s, ProofVersion, k) for k in keys]
            if len({v.environment_id for v in versions}) != 1:
                raise Invalid("Export each environment in a separate bundle")
            environment = required(s, Environment, versions[0].environment_id)
            if len({v.module for v in versions}) != len(versions):
                raise Invalid(
                    "Choose only one source version for each candidate/environment"
                )
            stream = io.BytesIO()
            records = []
            total_bytes = 0
            with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_DEFLATED) as z:
                for v in versions:
                    raw = required(s, Artifact, v.source_sha256).data
                    if hashlib.sha256(raw).hexdigest() != v.source_sha256:
                        raise Invalid("Stored source failed integrity check")
                    total_bytes += len(raw)
                    if total_bytes > 30 * 1024 * 1024:
                        raise Invalid(
                            "Export fewer candidates: source bundle exceeds 30 MiB"
                        )
                    path = v.module.replace(".", "/") + ".lean"
                    z.writestr(path, raw)
                    candidate = required(s, Candidate, v.candidate_id)
                    z.writestr(
                        "witnesses/" + v.candidate_id + ".json",
                        canonical(candidate.witness),
                    )
                    records.append(
                        {
                            **v.model_dump(mode="json"),
                            "path": path,
                            "statement": candidate.statement,
                        }
                    )
                manifest = {
                    "schema": "lcalc.candidate-bundle.v1",
                    "status": "unchecked-candidates",
                    "environment_id": environment.id,
                    "environment": environment.manifest,
                    "versions": records,
                    "notice": "These are proof scripts, not checked proofs. Run Lean under the recorded environment. Analytic results use the explicit ellipticModularity assumption.",
                }
                z.writestr("manifest.json", canonical(manifest))
                z.writestr(
                    "bundle-attestation.json", canonical(self.signer.envelope(manifest))
                )
                z.writestr(
                    "lean-toolchain",
                    environment.manifest["lean_toolchain"]
                    if "lean_toolchain" in environment.manifest
                    else self._toolchain(environment.manifest["lean"]),
                )
                z.writestr(
                    "Selection.lean",
                    selection_source([v.module for v in versions]),
                )
                z.writestr(
                    "Usage.lean",
                    usage_source(
                        [
                            (
                                v.module,
                                required(s, Candidate, v.candidate_id).statement[
                                    "analytic_rank"
                                ],
                            )
                            for v in versions
                        ]
                    ),
                )
                z.writestr(
                    "README.txt",
                    "UNCHECKED CANDIDATES\nUse lcalc-registry check-bundle BUNDLE.zip --public-key TRUSTED_PUBLIC_KEY.pem --output CHECK_DIR to check these with the installed matching environment.\nSelection.lean imports the resulting theorems.\nUsage.lean exports ImportedCertificates.Curve1.analytic_rank, etc., showing reuse without numerical recomputation.\nEach certificate exports analytic_rank; new certificates also export curve_analytic_rank and named witness equalities.\n",
                )
            return stream.getvalue()

    @staticmethod
    def _toolchain(version: str) -> str:
        import re

        match = re.search(r"version ([^, )]+)", version)
        if not match:
            raise Invalid("Environment lacks a Lean toolchain identifier")
        return "leanprover/lean4:v" + match[1].removeprefix("v") + "\n"

    def cached_certificate(
        self, candidate_id: str, environment_id: str
    ) -> SignedEnvelope[CacheManifest]:
        with Session(self.engine, expire_on_commit=False) as s:
            row = s.exec(
                select(Verification)
                .join(
                    ProofVersion,
                    col(ProofVersion.id) == col(Verification.proof_version_id),
                )
                .where(
                    col(ProofVersion.candidate_id) == candidate_id,
                    col(Verification.environment_id) == environment_id,
                    col(Verification.outcome) == "accepted",
                )
                .order_by(col(Verification.checked_at))
                .limit(1)
            ).first()
            if row is None:
                raise Missing("No accepted proof in this exact environment")
            return cast(SignedEnvelope[CacheManifest], row.envelope)

    def stats(self) -> dict[str, int]:
        with Session(self.engine, expire_on_commit=False) as s:
            return {
                model.__tablename__.removeprefix("registry_"): s.exec(
                    select(func.count()).select_from(model)
                ).one()
                for model in [
                    Source,
                    Curve,
                    Candidate,
                    ProofVersion,
                    Verification,
                    Campaign,
                ]
            }

    def renew_task(self, task_id: str, token: str, seconds: int) -> None:
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            task = self._owned(s, task_id, token)
            task.lease_until = now() + timedelta(seconds=seconds)
            s.add(task)

    def create_schedule(
        self,
        name: str,
        source_id: str,
        environment_id: str,
        interval_seconds: int,
        limit: int = 100,
    ) -> Schedule:
        if (
            not name
            or len(name) > 200
            or interval_seconds < 60
            or not 1 <= limit <= 1000
        ):
            raise Invalid(
                "Schedules require a name, interval >=60 seconds, and limit 1–1000"
            )
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            required(s, Source, source_id)
            required(s, Environment, environment_id)
            schedule = Schedule(
                name=name,
                source_id=source_id,
                environment_id=environment_id,
                interval_seconds=interval_seconds,
                limit=limit,
                next_due=now(),
            )
            s.add(schedule)
        return schedule

    def tick(self) -> Campaign | None:
        """Freeze one due campaign. SKIP LOCKED supports multiple scheduler processes."""
        timestamp = now()
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            schedule = s.exec(
                select(Schedule)
                .where(
                    col(Schedule.enabled).is_(True), col(Schedule.next_due) <= timestamp
                )
                .order_by(col(Schedule.next_due))
                .with_for_update(skip_locked=True)
                .limit(1)
            ).first()
            if schedule is None:
                return None
            versions = s.exec(
                select(ProofVersion)
                .join(Candidate, col(Candidate.id) == col(ProofVersion.candidate_id))
                .where(
                    col(ProofVersion.environment_id) == schedule.environment_id,
                    col(Candidate.curve_id).in_(
                        select(col(SourceCurve.curve_id)).where(
                            col(SourceCurve.source_id) == schedule.source_id
                        )
                    ),
                )
                .order_by(col(ProofVersion.id))
                .limit(schedule.limit)
            ).all()
            key = digest(
                {"schedule": schedule.id, "due": utc(schedule.next_due).isoformat()}
            )
            campaign = (
                self.create_campaign(
                    schedule.name,
                    [v.id for v in versions],
                    campaign_id=key,
                    session=s,
                    source_id=schedule.source_id,
                )
                if versions
                else None
            )
            # Coalesce missed intervals rather than enqueue an unbounded backlog.
            schedule.next_due = timestamp + timedelta(seconds=schedule.interval_seconds)
            s.add(schedule)
        return campaign

    def seal_ready_campaigns(self) -> None:
        with Session(self.engine, expire_on_commit=False) as s:
            # Recover the commit-before-seal crash window without rechecking proofs.
            ready = s.exec(
                select(col(Campaign.id))
                .where(
                    ~col(Campaign.id).in_(select(col(CampaignReport.campaign_id))),
                    ~col(Campaign.id).in_(
                        select(col(Task.campaign_id)).where(
                            col(Task.campaign_id).is_not(None),
                            col(Task.status).in_(["pending", "running"]),
                        )
                    ),
                )
                .order_by(col(Campaign.created_at))
                .limit(100)
            ).all()
        for key in ready:
            self.seal_campaign(key)

    def set_schedule_enabled(self, key: str, enabled: bool) -> Schedule:
        with Session(self.engine, expire_on_commit=False) as s, s.begin():
            value = s.exec(
                select(Schedule).where(col(Schedule.id) == key).with_for_update()
            ).first()
            if value is None:
                raise Missing("Schedule not found")
            value.enabled = bool(enabled)
            s.add(value)
        return value
