import hashlib
import secrets
from collections.abc import AsyncGenerator, Sequence
from contextlib import asynccontextmanager
from pathlib import Path

from fastapi import Depends, FastAPI, HTTPException, Query, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, JSONResponse, Response
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from pydantic import BaseModel, ConfigDict, Field, StrictInt, StrictStr
from sqlmodel import Session, col, select
from starlette.types import ASGIApp, Message, Receive, Scope, Send

from lcalc_registry.checker.protocol import Invalid

from .checker.contracts import CacheManifest, JsonObject, SignedEnvelope
from .config import Settings
from .db import engine_for, require_schema
from .mcp_server import create_mcp
from .models import (
    Artifact,
    Campaign,
    CampaignReport,
    Candidate,
    Environment,
    Installation,
    ProofVersion,
    Schedule,
    Source,
    SourceCurve,
    Task,
    Verification,
)
from .service import Missing, QueueFull, Registry
from .signing import Signer

BASE = Path(__file__).parent


class Input(BaseModel):
    model_config = ConfigDict(extra="forbid")


class CurveInput(BaseModel):
    model_config = ConfigDict(extra="ignore")  # Ignore unrelated database fields.
    label: str = Field(min_length=1, max_length=128)
    ainvs: list[StrictInt | StrictStr] = Field(min_length=5, max_length=5)
    conductor: StrictInt | StrictStr
    analytic_rank: StrictInt | StrictStr | None = None  # untrusted reference only


class ImportSource(Input):
    name: str = Field(min_length=1, max_length=200)
    inputs: list[CurveInput] = Field(min_length=1, max_length=10000)
    provenance: JsonObject = Field(default_factory=dict)


class Generate(Input):
    curve_ids: list[str] = Field(min_length=1, max_length=1000)
    environment_id: str


class ProofRequest(Input):
    source_id: str = Field(min_length=1, max_length=128)
    label: str = Field(min_length=1, max_length=128)
    environment_id: str = Field(min_length=1, max_length=128)
    witness: JsonObject | None = None


class Selection(Input):
    proof_version_ids: list[str] = Field(min_length=1, max_length=1000)


class Check(Selection):
    source_id: str | None = None
    name: str = Field(min_length=1, max_length=200)


class ScheduleUpdate(Input):
    enabled: bool


class NewSchedule(Input):
    name: str = Field(min_length=1, max_length=200)
    source_id: str
    environment_id: str
    interval_seconds: int = Field(ge=60)
    limit: int = Field(default=100, ge=1, le=1000)


class RequestLimits:
    """Bound bodies; HTTP MCP requires a bearer token, including read operations."""

    def __init__(self, app: ASGIApp, token: str | None) -> None:
        self.app = app
        self.token = token

    async def __call__(self, scope: Scope, receive: Receive, send: Send) -> None:
        if scope["type"] != "http":
            return await self.app(scope, receive, send)
        headers = dict(scope["headers"])
        if scope["path"].startswith("/mcp"):
            expected = ("Bearer " + self.token).encode() if self.token else None
            if expected is None or not secrets.compare_digest(
                headers.get(b"authorization", b""), expected
            ):
                return await Response(
                    "MCP requires the configured bearer token", status_code=401
                )(scope, receive, send)
        # Buffer once before handing the request to either framework. This also
        # enforces the bound for chunked bodies without Content-Length.
        chunks = []
        size = 0
        while True:
            message = await receive()
            if message["type"] == "http.disconnect":
                return
            chunk = message.get("body", b"")
            size += len(chunk)
            if size > 2 * 1024 * 1024:
                return await Response("Request exceeds 2 MiB", status_code=413)(
                    scope, receive, send
                )
            chunks.append(chunk)
            if not message.get("more_body", False):
                break
        sent = False

        async def replay() -> Message:
            nonlocal sent
            if not sent:
                sent = True
                return {
                    "type": "http.request",
                    "body": b"".join(chunks),
                    "more_body": False,
                }
            return await receive()

        async def with_headers(message: Message) -> None:
            if message["type"] == "http.response.start":
                message.setdefault("headers", []).append(
                    (b"x-content-type-options", b"nosniff")
                )
            await send(message)

        return await self.app(scope, replay, with_headers)


def create_app(
    settings: Settings | None = None, registry: Registry | None = None
) -> FastAPI:
    settings = settings or Settings()
    registry = registry or Registry(engine_for(settings), Signer(settings.data_dir))
    mcp = create_mcp(registry, settings)

    @asynccontextmanager
    async def lifespan(app: FastAPI) -> AsyncGenerator[None]:
        require_schema(registry.engine)
        async with mcp.session_manager.run():
            yield

    app = FastAPI(
        title="lcalc candidate and verification registry",
        version="0.1.0",
        lifespan=lifespan,
    )
    app.state.registry = registry
    app.state.mcp = mcp
    app.add_middleware(RequestLimits, token=settings.api_token)
    app.add_middleware(
        CORSMiddleware,
        allow_origins=list(settings.proof_origins),
        allow_methods=["GET", "POST"],
        allow_headers=["Content-Type"],
    )
    app.mount("/static", StaticFiles(directory=BASE / "static"), name="static")
    templates = Jinja2Templates(directory=BASE / "templates")

    def write_access(request: Request) -> None:
        expected = "Bearer " + settings.api_token if settings.api_token else None
        if expected is None or not secrets.compare_digest(
            request.headers.get("authorization", "").encode(), expected.encode()
        ):
            raise HTTPException(401, "A configured registry bearer token is required")

    @app.exception_handler(Invalid)
    async def invalid(request: Request, error: Invalid) -> JSONResponse:
        from fastapi.responses import JSONResponse

        return JSONResponse({"detail": str(error)}, status_code=400)

    @app.exception_handler(Missing)
    async def missing(request: Request, error: Missing) -> JSONResponse:
        from fastapi.responses import JSONResponse

        return JSONResponse({"detail": str(error)}, status_code=404)

    @app.get("/", response_class=HTMLResponse, include_in_schema=False)
    def home(request: Request) -> HTMLResponse:
        return templates.TemplateResponse(request, "index.html", {})

    @app.get("/healthz")
    def health() -> dict[str, str]:
        require_schema(registry.engine)
        return {"status": "ok"}

    @app.get("/v1/stats")
    def stats() -> dict[str, int]:
        return registry.stats()

    @app.get("/v1/sources")
    def sources() -> Sequence[Source]:
        return registry.sources()

    @app.post("/v1/sources", dependencies=[Depends(write_access)], status_code=201)
    def add_source(body: ImportSource) -> Source:
        return registry.import_source(
            body.name, [r.model_dump() for r in body.inputs], body.provenance
        )

    @app.get("/v1/environments")
    def environments() -> Sequence[Environment]:
        return registry.environments()

    @app.get("/v1/installations")
    def installations() -> Sequence[Installation]:
        with Session(registry.engine) as s:
            return s.exec(
                select(Installation).order_by(col(Installation.created_at).desc())
            ).all()

    @app.get("/v1/profiles")
    def profiles() -> list[JsonObject]:
        return [
            {"environment_id": e.id, "environment": e.manifest}
            for e in registry.environments()
        ]

    @app.get("/v1/curves")
    def curves(
        source_id: str | None = None,
        conductor: int | None = None,
        label: str | None = None,
        limit: int = Query(100, ge=1, le=1000),
        offset: int = Query(0, ge=0),
    ) -> list[JsonObject]:
        return registry.curves(source_id, conductor, label, limit, offset)

    @app.post("/v1/generate", dependencies=[Depends(write_access)], status_code=202)
    def generate(body: Generate) -> list[JsonObject]:
        return [
            t.model_dump(exclude={"lease_token"})
            for t in registry.enqueue_generation(body.curve_ids, body.environment_id)
        ]

    def request_status(task: Task) -> JsonObject:
        if not task.id.startswith("proof-request-"):
            raise HTTPException(404, "Proof request not found")
        version = task.result.get("proof_version_id")
        return {
            "id": task.id,
            "status": task.status,
            "error": task.error,
            "curve_id": task.curve_id,
            "environment_id": task.environment_id,
            "proof_version_id": version,
            "verification": "unchecked",
            "bundle_url": f"/v1/proof-requests/{task.id}/bundle" if version else None,
        }

    @app.post("/v1/witnesses", dependencies=[Depends(write_access)], status_code=202)
    def submit_witness(body: ProofRequest) -> JsonObject:
        if body.witness is None:
            raise HTTPException(400, "A numerical witness is required")
        return request_status(
            registry.request_proof(
                body.source_id,
                body.label,
                body.environment_id,
                body.witness,
                max_pending=settings.public_max_pending,
            )
        )

    @app.post("/v1/proof-requests", status_code=202)
    def proof_request(body: ProofRequest) -> JsonObject:
        if not settings.public_proof_requests:
            raise HTTPException(403, "Public proof requests are not enabled")
        return request_status(
            registry.request_proof(
                body.source_id,
                body.label,
                body.environment_id,
                body.witness,
                max_pending=settings.public_max_pending,
            )
        )

    @app.exception_handler(QueueFull)
    async def queue_full(request: Request, error: QueueFull) -> JSONResponse:
        return JSONResponse(
            {"detail": str(error)}, status_code=429, headers={"Retry-After": "30"}
        )

    @app.get("/v1/proof-requests/{key}")
    def proof_request_status(key: str) -> JsonObject:
        return request_status(registry.get(Task, key))

    @app.get("/v1/proof-requests/{key}/bundle")
    def proof_request_bundle(key: str) -> Response:
        task = registry.get(Task, key)
        request_status(task)
        version = task.result.get("proof_version_id")
        if not version:
            raise HTTPException(409, "Proof candidate is not ready")
        return Response(
            registry.proof_bundle([version]),
            media_type="application/zip",
            headers={
                "Content-Disposition": 'attachment; filename="unchecked-lean-proof.zip"'
            },
        )

    @app.get("/v1/proof-versions")
    def versions(
        curve_id: str | None = None,
        environment_id: str | None = None,
        source_id: str | None = None,
        limit: int = Query(100, ge=1, le=1000),
        offset: int = Query(0, ge=0),
    ) -> list[JsonObject]:
        return registry.versions(curve_id, environment_id, source_id, limit, offset)

    @app.get("/v1/proof-versions/{key}")
    def version(key: str) -> ProofVersion:
        return registry.get(ProofVersion, key)

    @app.get("/v1/proof-versions/{key}/source")
    def source(key: str) -> Response:
        v = registry.get(ProofVersion, key)
        raw = registry.get(Artifact, v.source_sha256).data
        if hashlib.sha256(raw).hexdigest() != v.source_sha256:
            raise HTTPException(500, "Stored source integrity failure")
        return Response(
            raw,
            media_type="text/plain",
            headers={"X-Lcalc-Artifact-SHA256": v.source_sha256},
        )

    @app.get("/v1/candidates/{key}")
    def candidate(key: str) -> Candidate:
        return registry.get(Candidate, key)

    @app.post("/v1/bundles")
    def bundle(body: Selection) -> Response:
        return Response(
            registry.proof_bundle(body.proof_version_ids),
            media_type="application/zip",
            headers={
                "Content-Disposition": 'attachment; filename="lcalc-candidates.zip"'
            },
        )

    @app.post("/v1/campaigns", dependencies=[Depends(write_access)], status_code=202)
    def campaign(body: Check) -> Campaign:
        return registry.create_campaign(
            body.name, body.proof_version_ids, source_id=body.source_id
        )

    @app.get("/v1/campaigns")
    def campaigns() -> Sequence[Campaign]:
        with Session(registry.engine) as s:
            return s.exec(
                select(Campaign).order_by(col(Campaign.created_at).desc()).limit(100)
            ).all()

    @app.get("/v1/campaigns/{key}")
    def campaign_status(key: str) -> JsonObject:
        return registry.campaign_status(key)

    @app.get("/v1/campaigns/{key}/report")
    def report(key: str) -> SignedEnvelope[JsonObject]:
        return registry.get(CampaignReport, key).envelope

    @app.get("/v1/tasks")
    def tasks(
        environment_id: str,
        source_id: str | None = None,
        limit: int = Query(100, ge=1, le=1000),
    ) -> list[JsonObject]:
        query = select(Task).where(
            col(Task.environment_id) == environment_id,
            col(Task.kind) == "generate",
        )
        if source_id is not None:
            query = query.where(
                col(Task.curve_id).in_(
                    select(col(SourceCurve.curve_id)).where(
                        col(SourceCurve.source_id) == source_id
                    )
                )
            )
        with Session(registry.engine) as session:
            rows = session.exec(
                query.order_by(col(Task.created_at).desc(), col(Task.id)).limit(limit)
            ).all()
            return [
                row.model_dump(mode="json", exclude={"lease_token"}) for row in rows
            ]

    @app.get("/v1/tasks/{key}")
    def task(key: str) -> JsonObject:
        return registry.get(Task, key).model_dump(exclude={"lease_token"})

    @app.get("/v1/verifications")
    def checks(
        proof_version_id: str | None = None, limit: int = Query(100, ge=1, le=1000)
    ) -> Sequence[Verification]:
        return registry.checks(proof_version_id, limit)

    @app.get("/v1/verifications/{key}")
    def check_record(key: str) -> Verification:
        from .models import Verification

        return registry.get(Verification, key)

    @app.post("/v1/schedules", dependencies=[Depends(write_access)], status_code=201)
    def schedule(body: NewSchedule) -> Schedule:
        return registry.create_schedule(**body.model_dump())

    @app.get("/v1/schedules")
    def schedules() -> Sequence[Schedule]:
        with Session(registry.engine) as s:
            return s.exec(select(Schedule).order_by(col(Schedule.next_due))).all()

    @app.patch("/v1/schedules/{key}", dependencies=[Depends(write_access)])
    def update_schedule(key: str, body: ScheduleUpdate) -> Schedule:
        return registry.set_schedule_enabled(key, body.enabled)

    @app.get("/v1/public-key")
    def public_key() -> Response:
        return Response(
            registry.signer.public_key(), media_type="application/x-pem-file"
        )

    @app.get("/v1/certificates/{key}")
    def cached(key: str, environment: str) -> SignedEnvelope[CacheManifest]:
        return registry.cached_certificate(key, environment)

    @app.get("/v1/objects/{key}")
    def obj(key: str) -> Response:
        value = registry.get(Artifact, key)
        if hashlib.sha256(value.data).hexdigest() != key:
            raise HTTPException(500, "Stored artifact integrity failure")
        return Response(value.data, media_type="application/octet-stream")

    app.mount("/mcp", mcp.streamable_http_app())
    return app
