import os
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Settings:
    database_url: str = field(
        default_factory=lambda: os.getenv(
            "REGISTRY_DATABASE_URL",
            "postgresql+psycopg://registry:registry@127.0.0.1:5432/lcalc_registry",
        )
    )
    data_dir: Path = field(
        default_factory=lambda: Path(
            os.getenv("REGISTRY_DATA_DIR", ROOT / ".registry-state")
        )
    )
    checker_root: Path = field(
        default_factory=lambda: Path(os.getenv("REGISTRY_CHECKER_ROOT", ROOT))
    )
    worker_build: Path | None = None
    api_token: str | None = field(
        default_factory=lambda: os.getenv("REGISTRY_API_TOKEN")
    )
    mcp_allowed_hosts: tuple[str, ...] = field(
        default_factory=lambda: tuple(
            os.getenv("REGISTRY_MCP_HOSTS", "127.0.0.1:*,localhost:*,[::1]:*").split(
                ","
            )
        )
    )
    public_proof_requests: bool = field(
        default_factory=lambda: os.getenv("REGISTRY_PUBLIC_PROOF_REQUESTS", "0") == "1"
    )
    public_max_pending: int = field(
        default_factory=lambda: int(os.getenv("REGISTRY_PUBLIC_MAX_PENDING", "64"))
    )
    proof_origins: tuple[str, ...] = field(
        default_factory=lambda: tuple(
            os.getenv(
                "REGISTRY_PROOF_ORIGINS", "https://www.lmfdb.org,https://lmfdb.org"
            ).split(",")
        )
    )
    task_lease_seconds: int = 1200
    check_timeout_seconds: int = 600
    allow_test_sqlite: bool = False
