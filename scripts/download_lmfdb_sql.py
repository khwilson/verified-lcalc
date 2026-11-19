#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = ["psycopg[binary]>=3.2,<4"]
# ///
"""Snapshot additional curves from the documented read-only SQL mirror.
Data plumbing only; reference ranks are never sent to the Lean producer.
Run: uv run scripts/download_lmfdb_sql.py
"""

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import socket
from collections.abc import Sequence
from decimal import Decimal
from pathlib import Path
from typing import Any

JsonObject = dict[str, Any]

ROOT = Path(__file__).resolve().parents[1]
QUERY = """SELECT lmfdb_label, conductor, array_to_json(ainvs)::text AS ainvs_json, analytic_rank
FROM ec_curvedata
WHERE NOT (lmfdb_label = ANY(%s))
ORDER BY conductor, lmfdb_label COLLATE "C"
LIMIT %s"""


def canonical(data: object) -> bytes:
    return (json.dumps(data, sort_keys=True, indent=2) + "\n").encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def excluded_labels(paths: list[Path]) -> list[str]:
    labels = []
    for path in paths:
        labels += [r["label"] for r in json.loads(path.read_text())["cases"]]
    if len(set(labels)) != len(labels):
        raise ValueError("Existing fixtures contain duplicate labels")
    return sorted(labels)


def validate_rows(
    rows: Sequence[Sequence[Any]], excluded: Sequence[str], count: int
) -> tuple[list[JsonObject], list[JsonObject]]:
    if len(rows) != count:
        raise ValueError(f"Expected {count} additional rows, received {len(rows)}")
    inputs, references, seen = [], [], set(excluded)
    previous = None
    for label, conductor, ainvs, rank in rows:
        if not isinstance(label, str) or not re.fullmatch(
            r"[1-9][0-9]*\.[a-z]+[1-9][0-9]*", label
        ):
            raise ValueError(f"Invalid curve label: {label!r}")
        if label in seen:
            raise ValueError(f"Duplicate/excluded curve: {label}")
        seen.add(label)
        if (
            not isinstance(conductor, int)
            or isinstance(conductor, bool)
            or conductor <= 0
            or int(label.split(".")[0]) != conductor
        ):
            raise ValueError(f"Invalid conductor for {label}")
        if isinstance(ainvs, str):
            ainvs = json.loads(ainvs, parse_float=Decimal)
        if isinstance(ainvs, (list, tuple)):
            ainvs = [
                int(a)
                if isinstance(a, Decimal) and a.is_finite() and a == int(a)
                else a
                for a in ainvs
            ]
        if (
            not isinstance(ainvs, (list, tuple))
            or len(ainvs) != 5
            or any(type(a) is not int for a in ainvs)
        ):
            raise ValueError(f"Invalid integral equation for {label}")
        if rank is not None and (type(rank) is not int or rank < 0):
            raise ValueError(f"Invalid analytic_rank for {label}")
        key = (conductor, label)
        if previous is not None and key <= previous:
            raise ValueError("SQL rows are not strictly ordered by conductor and label")
        previous = key
        inputs.append(dict(label=label, conductor=conductor, ainvs=list(ainvs)))
        references.append(dict(label=label, analytic_rank=rank))
    return inputs, references


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--count", type=int, default=10000)
    p.add_argument("--output", type=Path, default=ROOT / "data/lmfdb/sql-10000")
    p.add_argument("--exclude", type=Path, action="append")
    p.add_argument("--check-connectivity", action="store_true")
    args = p.parse_args()
    if args.count <= 0:
        p.error("--count must be positive")
    host = os.environ.get("LMFDB_HOST", "devmirror.lmfdb.xyz")
    port = int(os.environ.get("LMFDB_PORT", "5432"))
    # Detect unavailable network before asking uv/psycopg to install or connect.
    socket.getaddrinfo(host, port, type=socket.SOCK_STREAM)
    if args.check_connectivity:
        with socket.create_connection((host, port), timeout=10):
            print("SQL mirror TCP connection available")
        return
    import psycopg

    excluded = excluded_labels(
        args.exclude
        or [ROOT / "data/lmfdb-100.json", ROOT / "data/lmfdb-1000-additional.json"]
    )
    with psycopg.connect(
        host=host,
        port=port,
        dbname=os.environ.get("LMFDB_DBNAME", "lmfdb"),
        user=os.environ.get("LMFDB_USER", "lmfdb"),
        password=os.environ.get("LMFDB_PASSWORD", "lmfdb"),
        connect_timeout=10,
        application_name="verified-lcalc-snapshot",
    ) as conn:
        with conn.cursor() as cur:
            cur.execute("SET TRANSACTION ISOLATION LEVEL REPEATABLE READ, READ ONLY")
            cur.execute("SET LOCAL statement_timeout = '120s'")
            cur.execute("SELECT transaction_timestamp(), version()")
            snapshot_info = cur.fetchone()
            if snapshot_info is None:
                raise RuntimeError("SQL mirror returned no snapshot metadata")
            transaction_time, version = snapshot_info
            # The extra row detects a conductor truncated by the exact row limit.
            cur.execute(QUERY, (excluded, args.count + 1))
            all_rows = cur.fetchall()
            rows = all_rows[: args.count]
            inputs, references = validate_rows(rows, excluded, args.count)
            last = inputs[-1]["conductor"]
            cur.execute(
                "SELECT count(*) FROM ec_curvedata WHERE conductor = %s AND NOT (lmfdb_label = ANY(%s))",
                (last, excluded),
            )
            boundary = cur.fetchone()
            if boundary is None:
                raise RuntimeError("SQL mirror returned no conductor boundary count")
            boundary_available = boundary[0]
    raw = dict(
        columns=["lmfdb_label", "conductor", "ainvs_json", "analytic_rank"], rows=rows
    )
    # Normalize possible JSON-encoded ainvs to keep the raw capture JSON writable.
    raw_bytes = canonical(raw)
    input_bytes = canonical(dict(inputs=inputs))
    reference_bytes = canonical(dict(references=references))
    provenance = dict(
        source="https://www.lmfdb.org/api/options",
        table="ec_curvedata",
        sql=QUERY,
        parameters=dict(excluded_labels=excluded, limit=args.count + 1),
        host=host,
        port=port,
        database=os.environ.get("LMFDB_DBNAME", "lmfdb"),
        transaction_time=transaction_time.isoformat(),
        postgres_version=version,
        retrieved_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
        count=len(inputs),
        excluded_count=len(excluded),
        excluded_sha256=digest(canonical(excluded)),
        first_conductor=inputs[0]["conductor"],
        last_conductor=last,
        last_conductor_selected=sum(r["conductor"] == last for r in inputs),
        last_conductor_available=boundary_available,
        boundary_conductor_complete=sum(r["conductor"] == last for r in inputs)
        == boundary_available,
        license="LMFDB CC-BY-SA; https://www.lmfdb.org/api/options",
        attribution="The LMFDB Collaboration; https://www.lmfdb.org/citation",
        raw_sha256=digest(raw_bytes),
        inputs_sha256=digest(input_bytes),
        references_sha256=digest(reference_bytes),
    )
    args.output.mkdir(parents=True, exist_ok=True)
    for name, data in [
        ("raw.json", raw_bytes),
        ("inputs.json", input_bytes),
        ("references.json", reference_bytes),
        ("provenance.json", canonical(provenance)),
    ]:
        target = args.output / name
        if target.exists() and target.read_bytes() != data:
            raise FileExistsError(f"Refusing to replace a different snapshot: {target}")
    for name, data in [
        ("raw.json", raw_bytes),
        ("inputs.json", input_bytes),
        ("references.json", reference_bytes),
        ("provenance.json", canonical(provenance)),
    ]:
        (args.output / name).write_bytes(data)
    print(json.dumps(provenance, indent=2))


if __name__ == "__main__":
    main()
