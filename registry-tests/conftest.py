from collections.abc import Generator
from pathlib import Path

import pytest
from support import RegistryFixture

from lcalc_registry.config import Settings
from lcalc_registry.db import engine_for, migrate
from lcalc_registry.service import Registry
from lcalc_registry.signing import Signer


@pytest.fixture
def setup(tmp_path: Path) -> Generator[RegistryFixture]:
    settings = Settings(
        database_url=f"sqlite:///{tmp_path}/registry.sqlite3",
        data_dir=tmp_path / "state",
        api_token="test-operator-token",
        allow_test_sqlite=True,
    )
    engine = engine_for(settings)
    migrate(engine)
    signer = Signer(settings.data_dir)
    signer.initialize()
    registry = Registry(engine, signer)
    yield settings, registry
    engine.dispose()
