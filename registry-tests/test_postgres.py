"""Runs only against an explicitly supplied disposable local PostgreSQL database."""

import os
from collections.abc import Generator
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from uuid import uuid4

import pytest
from sqlalchemy import text
from sqlalchemy.exc import DatabaseError
from support import RegistryFixture
from test_registry import FakeBackend, base

from lcalc_registry.config import Settings
from lcalc_registry.db import engine_for, migrate
from lcalc_registry.service import Registry
from lcalc_registry.signing import Signer
from lcalc_registry.worker import Worker

pytestmark = pytest.mark.postgres


@pytest.fixture
def pg(tmp_path: Path) -> Generator[RegistryFixture]:
    url = os.getenv("REGISTRY_TEST_DATABASE_URL")
    if not url:
        pytest.skip(
            "Set REGISTRY_TEST_DATABASE_URL to run actual PostgreSQL integration tests"
        )
    settings = Settings(database_url=url, data_dir=tmp_path / "state")
    owner = engine_for(settings)
    schema = "registry_test_" + uuid4().hex
    with owner.begin() as c:
        c.execute(text(f"CREATE SCHEMA {schema}"))
    isolated = owner.url.update_query_dict(
        {"options": "-csearch_path=" + schema}
    ).render_as_string(hide_password=False)
    engine = engine_for(replace(settings, database_url=isolated))
    migrate(engine)
    signer = Signer(settings.data_dir)
    signer.initialize()
    registry = Registry(engine, signer)
    try:
        yield replace(settings, database_url=isolated), registry
    finally:
        engine.dispose()
        with owner.begin() as c:
            c.execute(text(f"DROP SCHEMA {schema} CASCADE"))
        owner.dispose()


def test_pg_jsonb_triggers_and_concurrent_skip_locked_claims(
    pg: RegistryFixture,
) -> None:
    settings, reg = pg
    env, src, curve = base(reg)
    for _ in range(8):
        reg.enqueue_generation([curve["id"]], env.id)
    with ThreadPoolExecutor(max_workers=8) as pool:
        claimed = list(pool.map(lambda _: reg.claim(env.id, 180), range(8)))
    assert len({t.id for t in claimed if t is not None}) == 8
    assert reg.claim(env.id, 180) is None
    with pytest.raises(DatabaseError):
        with reg.engine.begin() as c:
            c.execute(
                text("UPDATE registry_source SET name=:name WHERE id=:key"),
                {"name": "tampered", "key": src.id},
            )
    with reg.engine.connect() as c:
        assert (
            c.execute(
                text(
                    "SELECT data_type FROM information_schema.columns WHERE table_schema=current_schema() AND table_name='registry_curve' AND column_name='subject'"
                )
            ).scalar_one()
            == "jsonb"
        )


def test_pg_duplicate_generation_and_campaign_record(pg: RegistryFixture) -> None:
    settings, reg = pg
    env, src, curve = base(reg)
    backend = FakeBackend(env)
    reg.enqueue_generation([curve["id"]], env.id)
    reg.enqueue_generation([curve["id"]], env.id)
    with ThreadPoolExecutor(max_workers=2) as pool:
        list(pool.map(lambda _: Worker(reg, backend, settings).once(), range(2)))
    versions = reg.versions()
    assert len(versions) == 1
    campaign = reg.create_campaign("PostgreSQL test", [versions[0]["id"]])
    Worker(reg, backend, settings).once()
    assert reg.campaign_status(campaign.id)["complete"]
    assert len(reg.checks()) == 1


def test_pg_public_request_idempotency_and_admission_lock(pg: RegistryFixture) -> None:
    from test_registry import witness

    from lcalc_registry.service import QueueFull

    settings, reg = pg
    env, src, curve = base(reg)
    with ThreadPoolExecutor(max_workers=8) as pool:
        tasks = list(
            pool.map(
                lambda _: reg.request_proof(src.id, "37.a1", env.id, max_pending=1),
                range(8),
            )
        )
    assert len({task.id for task in tasks}) == 1
    with pytest.raises(QueueFull):
        reg.request_proof(
            src.id, "37.a1", env.id, witness(curve["subject"]), max_pending=1
        )
    assert Worker(reg, FakeBackend(env), settings).once()
    assert reg.request_proof(src.id, "37.a1", env.id, max_pending=1).id == tasks[0].id
