"""Curated MCP tools share Registry operations with HTTP; no arbitrary SQL/Lean."""

import base64

from mcp.server.fastmcp import FastMCP
from mcp.server.transport_security import TransportSecuritySettings
from mcp.types import ToolAnnotations

from .checker.contracts import JsonObject
from .config import Settings
from .service import Registry

READ = ToolAnnotations(readOnlyHint=True, destructiveHint=False)
WRITE = ToolAnnotations(readOnlyHint=False, destructiveHint=False)


def create_mcp(registry: Registry, settings: Settings | None = None) -> FastMCP:
    settings = settings or Settings()
    server = FastMCP(
        "lcalc-registry",
        stateless_http=True,
        json_response=True,
        streamable_http_path="/",
        transport_security=TransportSecuritySettings(
            allowed_hosts=list(settings.mcp_allowed_hosts)
        ),
        instructions="Generated proof candidates are UNCHECKED. Only accepted verification records attest a check in their exact environment. Analytic results currently depend on ellipticModularity.",
    )

    @server.tool(annotations=READ)
    def list_sources() -> list[JsonObject]:
        """List immutable source-data snapshots and their provenance."""
        return [s.model_dump(mode="json") for s in registry.sources()]

    @server.tool(annotations=READ)
    def list_environments() -> list[JsonObject]:
        """List exact Lean/mathlib/checker profiles registered by the operator."""
        return [s.model_dump(mode="json") for s in registry.environments()]

    @server.tool(annotations=READ)
    def find_curves(
        source_id: str | None = None,
        conductor: int | None = None,
        label: str | None = None,
        limit: int = 100,
        offset: int = 0,
    ) -> list[JsonObject]:
        """Find exact curve inputs; labels are scoped to source snapshots."""
        return registry.curves(source_id, conductor, label, limit, offset)

    @server.tool(annotations=READ)
    def find_proof_candidates(
        curve_id: str | None = None,
        environment_id: str | None = None,
        source_id: str | None = None,
        limit: int = 100,
        offset: int = 0,
    ) -> list[JsonObject]:
        """Find generated proof scripts and dated check status; existence is not verification."""
        return registry.versions(curve_id, environment_id, source_id, limit, offset)

    @server.tool(annotations=WRITE)
    def import_source_snapshot(
        name: str, inputs: list[JsonObject], provenance: JsonObject
    ) -> JsonObject:
        """Import immutable inputs and external reference ranks. Reference answers never drive proof construction."""
        return registry.import_source(name, inputs, provenance).model_dump(mode="json")

    @server.tool(annotations=WRITE)
    def generate_candidates(
        curve_ids: list[str], environment_id: str
    ) -> list[JsonObject]:
        """Queue cheap Lean candidate generation. Does NOT queue expensive kernel checks."""
        return [
            t.model_dump(mode="json", exclude={"lease_token"})
            for t in registry.enqueue_generation(curve_ids, environment_id)
        ]

    @server.tool(annotations=WRITE)
    def submit_numerical_witness(
        source_id: str,
        label: str,
        environment_id: str,
        witness: JsonObject,
    ) -> JsonObject:
        """Freeze a numerical witness and queue unchecked Lean source, without search or kernel checking."""
        return registry.request_proof(
            source_id,
            label,
            environment_id,
            witness,
            max_pending=settings.public_max_pending,
        ).model_dump(mode="json", exclude={"lease_token"})

    @server.tool(annotations=WRITE)
    def request_verification(
        name: str, proof_version_ids: list[str], source_id: str | None = None
    ) -> JsonObject:
        """Explicitly request expensive decide +kernel checking for this frozen selection."""
        return registry.create_campaign(
            name, proof_version_ids, source_id=source_id
        ).model_dump(mode="json")

    @server.tool(annotations=READ)
    def task_status(task_id: str) -> JsonObject:
        """Read generation or checking progress without exposing worker lease credentials."""
        from .models import Task

        return registry.get(Task, task_id).model_dump(
            mode="json", exclude={"lease_token"}
        )

    @server.tool(annotations=READ)
    def verification_status(campaign_id: str) -> JsonObject:
        """Get per-member outcomes for a requested verification campaign."""
        return registry.campaign_status(campaign_id)

    @server.tool(annotations=READ)
    def list_verification_records(
        proof_version_id: str | None = None, limit: int = 100
    ) -> list[JsonObject]:
        """Read dated, immutable check attempts, including rejected attempts."""
        return [
            r.model_dump(mode="json") for r in registry.checks(proof_version_id, limit)
        ]

    @server.tool(annotations=WRITE)
    def set_schedule_enabled(schedule_id: str, enabled: bool) -> JsonObject:
        """Pause or resume future scheduled campaigns. Existing campaigns are unchanged."""
        return registry.set_schedule_enabled(schedule_id, enabled).model_dump(
            mode="json"
        )

    @server.tool(annotations=READ)
    def export_proof_bundle(proof_version_ids: list[str]) -> JsonObject:
        """Export an UNCHECKED source bundle for local checking. Returns a base64 ZIP."""
        # Keep MCP responses bounded; larger exports are available via HTTP/CLI.
        if len(proof_version_ids) > 20:
            raise ValueError("Use the HTTP export endpoint for more than 20 proofs")
        raw = registry.proof_bundle(proof_version_ids)
        if len(raw) > 2 * 1024 * 1024:
            raise ValueError("Use the HTTP export endpoint for this large proof bundle")
        return {
            "status": "unchecked-candidates",
            "media_type": "application/zip",
            "base64": base64.b64encode(raw).decode(),
        }

    return server
