"""Versioned PostgreSQL bootstrap, queue locks and append-only evidence tables."""

import sqlite3

from sqlalchemy import event, text
from sqlalchemy.engine import Engine
from sqlmodel import SQLModel, create_engine

from .config import Settings

IMMUTABLE = [
    "source",
    "curve",
    "source_curve",
    "environment",
    "installation",
    "artifact",
    "candidate",
    "proof_version",
    "verification",
    "campaign",
    "campaign_member",
    "campaign_report",
]


def engine_for(settings: Settings) -> Engine:
    url = settings.database_url
    if url.startswith("postgresql://"):
        url = url.replace("postgresql://", "postgresql+psycopg://", 1)
    if not url.startswith("postgresql+psycopg://") and not (
        settings.allow_test_sqlite and url.startswith("sqlite")
    ):
        raise ValueError(
            "The registry requires PostgreSQL; SQLite is only an explicit unit-test adapter"
        )
    options = {"pool_pre_ping": True}
    if url.startswith("sqlite"):
        options["connect_args"] = {"check_same_thread": False}
    engine = create_engine(url, **options)
    if engine.dialect.name == "sqlite":

        @event.listens_for(engine, "connect")
        def foreign_keys(connection: sqlite3.Connection, _: object) -> None:
            connection.execute("PRAGMA foreign_keys=ON")

    return engine


def migrate(engine: Engine) -> None:
    """Run explicitly with the migration owner, never on API startup."""
    with engine.begin() as connection:
        pg = engine.dialect.name == "postgresql"
        if pg:
            connection.execute(text("SELECT pg_advisory_xact_lock(824630191)"))
        connection.execute(
            text(
                "CREATE TABLE IF NOT EXISTS registry_schema_version (version INTEGER PRIMARY KEY)"
            )
        )
        versions = list(
            connection.execute(
                text("SELECT version FROM registry_schema_version")
            ).scalars()
        )
        if versions and versions != [1]:
            raise RuntimeError("Unsupported registry schema version")
        if versions:
            return
        SQLModel.metadata.create_all(connection)
        if pg:
            connection.execute(
                text("""CREATE OR REPLACE FUNCTION registry_evidence_immutable() RETURNS trigger LANGUAGE plpgsql AS $$
                BEGIN RAISE EXCEPTION 'Registry evidence is append-only'; END; $$""")
            )
            for table in IMMUTABLE:
                name = "registry_" + table
                connection.execute(
                    text(
                        f"CREATE TRIGGER evidence_immutable BEFORE UPDATE OR DELETE ON {name} FOR EACH ROW EXECUTE FUNCTION registry_evidence_immutable()"
                    )
                )
        else:
            for table in IMMUTABLE:
                name = "registry_" + table
                for action in ["UPDATE", "DELETE"]:
                    connection.execute(
                        text(
                            f"CREATE TRIGGER {name}_{action.lower()} BEFORE {action} ON {name} BEGIN SELECT RAISE(ABORT, 'Registry evidence is append-only'); END"
                        )
                    )
        connection.execute(text("INSERT INTO registry_schema_version VALUES (1)"))


def require_schema(engine: Engine) -> None:
    with engine.connect() as connection:
        versions = list(
            connection.execute(
                text("SELECT version FROM registry_schema_version")
            ).scalars()
        )
        if versions != [1]:
            raise RuntimeError(
                "Run lcalc-registry migrate using the migration owner first"
            )
