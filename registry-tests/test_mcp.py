import asyncio

import anyio
import httpx
from mcp import ClientSession
from mcp.client.streamable_http import streamable_http_client
from mcp.types import TextContent
from support import RegistryFixture
from test_registry import base, witness

from lcalc_registry.api import create_app


def test_real_mcp_protocol_over_asgi_shares_database(setup: RegistryFixture) -> None:
    settings, registry = setup
    env, src, curve = base(registry)
    app = create_app(settings, registry)
    token = settings.api_token
    assert token is not None

    async def exercise() -> None:
        with anyio.fail_after(15):
            async with app.router.lifespan_context(app):
                async with httpx.AsyncClient(
                    transport=httpx.ASGITransport(app=app),
                    base_url="http://localhost:8788",
                    headers={"Authorization": "Bearer " + token},
                ) as http:
                    async with streamable_http_client(
                        "http://localhost:8788/mcp/", http_client=http
                    ) as (read, write, _):
                        async with ClientSession(read, write) as session:
                            await session.initialize()
                            tools = await session.list_tools()
                            assert "request_verification" in {
                                t.name for t in tools.tools
                            }
                            assert not any(
                                "record_check" in t.name or "sql" in t.name
                                for t in tools.tools
                            )
                            result = await session.call_tool(
                                "find_curves", {"source_id": src.id}
                            )
                            assert not result.isError
                            content = result.content[0]
                            assert isinstance(content, TextContent)
                            assert "37.a1" in content.text
                            result = await session.call_tool(
                                "generate_candidates",
                                {"curve_ids": [curve["id"]], "environment_id": env.id},
                            )
                            assert not result.isError
                            submitted = await session.call_tool(
                                "submit_numerical_witness",
                                {
                                    "source_id": src.id,
                                    "label": "37.a1",
                                    "environment_id": env.id,
                                    "witness": witness(curve["subject"]),
                                },
                            )
                            assert not submitted.isError
                            assert registry.stats()["verification"] == 0

    asyncio.run(exercise())
