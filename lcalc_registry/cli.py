"""uv run lcalc-registry --help"""

import argparse
import json
import time
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from sqlmodel import SQLModel

from .config import Settings
from .db import engine_for, migrate, require_schema
from .service import Registry
from .signing import Signer


def out(value: SQLModel | Mapping[str, Any]) -> None:
    if isinstance(value, SQLModel):
        value = value.model_dump(mode="json", exclude={"lease_token"})
    print(json.dumps(value, indent=2, default=str))


def main() -> None:
    p = argparse.ArgumentParser(
        description="Lean candidate generation and dated verification registry"
    )
    p.add_argument("--database-url", help="Defaults to REGISTRY_DATABASE_URL")
    p.add_argument("--data-dir", type=Path)
    p.add_argument("--checker-root", type=Path)
    p.add_argument("--worker-build", type=Path)
    sub = p.add_subparsers(dest="command", required=True)
    sub.add_parser("build-worker", help="Build only the minimal Lean numerical worker")
    sub.add_parser(
        "migrate", help="Apply numbered schema migrations; run with the migration owner"
    )
    sub.add_parser(
        "init-keys",
        help="Create operator signing keys; never overwrite an existing private key",
    )
    sub.add_parser(
        "register-environment",
        help="Register the locally installed exact checker profile",
    )
    imp = sub.add_parser(
        "import",
        help="Import immutable inputs and separately recorded reference claims",
    )
    imp.add_argument("file", type=Path)
    imp.add_argument("--name", required=True)
    imp.add_argument("--provenance", type=Path)
    imp.add_argument(
        "--references",
        type=Path,
        help="Separate label/analytic_rank records; stored only as external claims",
    )
    gen = sub.add_parser(
        "generate", help="Queue candidate generation without kernel checking"
    )
    gen.add_argument("--source", required=True)
    gen.add_argument("--environment", required=True)
    gen.add_argument("--conductor", type=int)
    gen.add_argument("--limit", type=int, default=1000)
    gen.add_argument("--offset", type=int, default=0)
    submit = sub.add_parser(
        "submit-witness", help="Queue unchecked Lean source from numerical JSON"
    )
    submit.add_argument("file", type=Path)
    submit.add_argument("--source", required=True)
    submit.add_argument("--label", required=True)
    submit.add_argument("--environment", required=True)
    serve = sub.add_parser("serve")
    serve.add_argument("--host", default="127.0.0.1")
    serve.add_argument("--port", type=int, default=8788)
    worker = sub.add_parser("worker")
    worker.add_argument("--once", action="store_true")
    sub.add_parser("mcp", help="Run the local, trusted stdio MCP server")
    camp = sub.add_parser(
        "campaign", help="Queue an explicit, frozen verification selection"
    )
    camp.add_argument("versions", nargs="+")
    camp.add_argument("--name", required=True)
    camp.add_argument(
        "--source", help="Compare checked ranks with this frozen source snapshot"
    )
    export = sub.add_parser("export")
    export.add_argument("versions", nargs="+")
    export.add_argument("--output", required=True, type=Path)
    local = sub.add_parser(
        "check-bundle", help="Locally kernel-check a signed candidate bundle"
    )
    local.add_argument("bundle", type=Path)
    local.add_argument("--output", required=True, type=Path)
    local.add_argument("--public-key", required=True, type=Path)
    cache = sub.add_parser(
        "cache",
        help="Fetch accepted proof artifacts without repeating numerical checking",
    )
    cache.add_argument("certificate_id")
    cache.add_argument("--url", required=True)
    cache.add_argument("--public-key", required=True, type=Path)
    cache.add_argument("--directory", type=Path, default=Path(".lcalc-cache"))
    cache.add_argument("--check", type=Path)
    status = sub.add_parser("status")
    status.add_argument("campaign_id", nargs="?")
    sched = sub.add_parser("schedule")
    sched.add_argument("--name", required=True)
    sched.add_argument("--source", required=True)
    sched.add_argument("--environment", required=True)
    sched.add_argument("--every", type=int, default=86400)
    sched.add_argument("--limit", type=int, default=100)
    pause = sub.add_parser("pause-schedule")
    pause.add_argument("schedule_id")
    pause.add_argument("--resume", action="store_true")
    scheduler = sub.add_parser("scheduler")
    scheduler.add_argument("--once", action="store_true")
    args = p.parse_args()
    defaults = Settings()
    settings = Settings(
        database_url=args.database_url or defaults.database_url,
        data_dir=args.data_dir or defaults.data_dir,
        checker_root=(args.checker_root or defaults.checker_root).resolve(),
        worker_build=args.worker_build,
        api_token=defaults.api_token,
    )
    signer = Signer(settings.data_dir)
    if args.command == "submit-witness":
        engine = engine_for(settings)
        require_schema(engine)
        registry = Registry(engine, signer)
        out(
            registry.request_proof(
                args.source,
                args.label,
                args.environment,
                json.loads(args.file.read_text()),
                max_pending=settings.public_max_pending,
            )
        )
        return
    if args.command == "init-keys":
        signer.initialize()
        out({"public_key": str(settings.data_dir / "signing-public.pem")})
        return
    if args.command == "check-bundle":
        from .bundles import check_bundle

        out(check_bundle(args.bundle, args.output, args.public_key, settings))
        return
    if args.command == "cache":
        import os
        import subprocess

        from .cache import RegistryCache
        from .consumer import installed

        env = installed(settings)
        result = RegistryCache(
            args.url, args.public_key, args.directory, env.public
        ).fetch(args.certificate_id)
        out(result)
        if args.check:
            subprocess.run(
                [str(env.lean), str(args.check)],
                env={
                    **os.environ,
                    "LEAN_PATH": result["lean_path"] + ":" + env.lean_path,
                    "LEAN_NUM_THREADS": "1",
                },
                check=True,
            )
        return
    if args.command == "build-worker":
        from .tools.build_native import main as build_worker

        build_worker()
        return
    engine = engine_for(settings)
    if args.command == "migrate":
        migrate(engine)
        out({"schema_version": 1})
        return
    require_schema(engine)
    registry = Registry(engine, signer)
    if args.command == "register-environment":
        from .backend import NativeBackend

        backend = NativeBackend(settings)
        value = registry.register_environment(backend.manifest, backend.implementation)
        from .service import installation_id

        out(
            {
                "environment_id": value.id,
                "installation_id": installation_id(value.id, backend.implementation),
                "environment": value.manifest,
            }
        )
    elif args.command == "import":
        raw = json.loads(args.file.read_text())
        rows = raw if isinstance(raw, list) else raw.get("inputs", raw.get("cases", []))
        provenance = (
            json.loads(args.provenance.read_text())
            if args.provenance
            else {
                "input_file": args.file.name,
                "input_file_sha256": __import__("hashlib")
                .sha256(args.file.read_bytes())
                .hexdigest(),
            }
        )
        if args.references:
            reference_raw = json.loads(args.references.read_text())
            reference_rows = (
                reference_raw
                if isinstance(reference_raw, list)
                else reference_raw.get("references", [])
            )
            references = {r["label"]: r["analytic_rank"] for r in reference_rows}
            if len(references) != len(reference_rows) or set(references) != {
                r["label"] for r in rows
            }:
                raise ValueError(
                    "Reference labels must exactly match the unique input labels"
                )
            rows = [{**row, "analytic_rank": references[row["label"]]} for row in rows]
            provenance = {
                **provenance,
                "reference_file_sha256": __import__("hashlib")
                .sha256(args.references.read_bytes())
                .hexdigest(),
            }
        out(registry.import_source(args.name, rows, provenance))
    elif args.command == "generate":
        rows = registry.curves(
            args.source, args.conductor, limit=args.limit, offset=args.offset
        )
        tasks = registry.enqueue_generation([r["id"] for r in rows], args.environment)
        out(
            {
                "tasks": [t.id for t in tasks],
                "status": "candidate-generation-queued",
                "kernel_verification_requested": False,
            }
        )
    elif args.command == "serve":
        import uvicorn

        from .api import create_app

        uvicorn.run(create_app(settings, registry), host=args.host, port=args.port)
    elif args.command == "mcp":
        from .mcp_server import create_mcp

        create_mcp(registry, settings).run()
    elif args.command == "worker":
        import logging

        logging.basicConfig(
            level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s"
        )
        from .backend import NativeBackend
        from .worker import Worker

        logging.getLogger(__name__).info(
            "Initializing worker and checking registered installation…"
        )
        worker = Worker(registry, NativeBackend(settings), settings)
        logging.getLogger(__name__).info(
            "Worker ready; polling every second. Environment %s; installation %s",
            worker.backend.id,
            worker.installation_id,
        )
        while True:
            worked = worker.once()
            if args.once:
                out({"processed": worked})
                break
            if not worked:
                time.sleep(1)
    elif args.command == "campaign":
        out(registry.create_campaign(args.name, args.versions, source_id=args.source))
    elif args.command == "export":
        args.output.write_bytes(registry.proof_bundle(args.versions))
        out({"path": str(args.output), "status": "unchecked-candidates"})
    elif args.command == "status":
        out(
            registry.campaign_status(args.campaign_id)
            if args.campaign_id
            else registry.stats()
        )
    elif args.command == "schedule":
        out(
            registry.create_schedule(
                args.name, args.source, args.environment, args.every, args.limit
            )
        )
    elif args.command == "pause-schedule":
        out(registry.set_schedule_enabled(args.schedule_id, args.resume))
    elif args.command == "scheduler":
        while True:
            campaign = registry.tick()
            if campaign:
                out(campaign)
            registry.seal_ready_campaigns()
            if args.once:
                break
            time.sleep(1)


if __name__ == "__main__":
    main()
