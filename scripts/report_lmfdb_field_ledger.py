"""Join native LMFDB rows, producer routes, and audited consumer evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any

if __package__:
    from . import produce_ec_witness as producer
    from .capture_lmfdb_fixture import replay_capture_bytes
else:
    import produce_ec_witness as producer
    from capture_lmfdb_fixture import replay_capture_bytes

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_NATIVE = ROOT / "tests/fixtures/lmfdb/112.a2-native.json"
DEFAULT_COVERAGE = ROOT / "web/certificates/fixture-field-coverage.json"
DEFAULT_NEXT_STEPS = ROOT / "docs/roadmaps/lmfdb-producer-next-steps.json"
LEDGER_SCHEMA = "lcalc.lmfdb-field-ledger.v1"


class ExactNumber(str):
    """A non-integral JSON number retaining its source token spelling."""


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def exact_json(value: Any) -> str:
    """Serialize parsed JSON while preserving every non-integral number token."""
    if isinstance(value, ExactNumber):
        return str(value)
    if isinstance(value, list):
        return "[" + ",".join(exact_json(item) for item in value) + "]"
    if isinstance(value, dict):
        return (
            "{"
            + ",".join(
                json.dumps(key, ensure_ascii=False) + ":" + exact_json(item)
                for key, item in value.items()
            )
            + "}"
        )
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def json_kind(value: Any) -> str:
    if isinstance(value, ExactNumber) or (
        isinstance(value, int) and not isinstance(value, bool)
    ):
        return "number"
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "boolean"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "array"
    if isinstance(value, dict):
        return "object"
    raise ValueError(f"Unsupported JSON value {type(value).__name__}")


def decode_exact(raw: bytes, source: str) -> dict[str, Any]:
    def reject_constant(token: str) -> None:
        raise ValueError(f"Invalid JSON constant {token}")

    try:
        value = json.loads(
            raw,
            object_pairs_hook=unique_object,
            parse_float=ExactNumber,
            parse_constant=reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"Invalid JSON in {source}: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"Expected a JSON object in {source}")
    return value


def read_json(path: Path) -> dict[str, Any]:
    return decode_exact(path.read_bytes(), str(path))


def canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def validate_inputs(
    native_path: Path,
    manifest_path: Path,
    coverage_path: Path,
    next_steps_path: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], str]:
    raw = native_path.read_bytes()
    native = decode_exact(raw, str(native_path))
    manifest = read_json(manifest_path)
    coverage = read_json(coverage_path)
    next_steps = read_json(next_steps_path)
    replay_input_sha256 = hashlib.sha256(
        replay_capture_bytes(raw, manifest)
    ).hexdigest()

    if coverage.get("schema") != "lcalc.fixture-field-coverage.v1":
        raise ValueError("Unexpected audited fixture coverage schema")
    fields = coverage.get("fields")
    if not isinstance(fields, list) or coverage.get("table_qualified_fields") != 101:
        raise ValueError("Audited coverage denominator is not the expected 101 entries")
    keys = [(entry.get("table"), entry.get("field")) for entry in fields]
    if len(keys) != 101 or len(set(keys)) != 101:
        raise ValueError(
            "Coverage catalogue has missing or repeated table-qualified fields"
        )
    if len({field for _, field in keys}) != 85 or coverage.get("distinct_names") != 85:
        raise ValueError("Coverage catalogue no longer has 85 distinct field names")
    expected = {f"{table}.{field}" for table, field in keys}
    if set(next_steps) != expected:
        raise ValueError("Next-steps map must cover exactly the 101 catalogue entries")
    if not all(
        isinstance(action, str) and action.strip() for action in next_steps.values()
    ):
        raise ValueError("Every field needs a nonempty concrete next step")
    return native, manifest, coverage, next_steps, replay_input_sha256


def observations_for(
    native: dict[str, Any], manifest_table: dict[str, Any], field: str
) -> tuple[str, str, list[dict[str, Any]]]:
    table = manifest_table["name"]
    table_names = native["tables"]
    if table not in table_names:
        return "not_captured", "not_captured", []
    index = table_names.index(table)
    rows = native["data"][index]
    if not rows:
        return "no_rows", "no_rows", []
    if len(rows) != len(manifest_table["row_keys"]):
        raise ValueError(f"Row count mismatch in {table}")
    observations = []
    for row_key, row in zip(manifest_table["row_keys"], rows, strict=True):
        if not isinstance(row, dict):
            raise ValueError(f"Expected object row in {table}")
        if field not in row:
            observations.append(
                {
                    "row_key_name": _row_key_name(table),
                    "row_key": row_key,
                    "state": "field_absent",
                    "json_type": None,
                    "value_json": None,
                }
            )
        elif row[field] is None:
            observations.append(
                {
                    "row_key_name": _row_key_name(table),
                    "row_key": row_key,
                    "state": "json_null",
                    "json_type": "null",
                    "value_json": "null",
                }
            )
        else:
            value = row[field]
            observations.append(
                {
                    "row_key_name": _row_key_name(table),
                    "row_key": row_key,
                    "state": "empty_array" if value == [] else "value",
                    "json_type": json_kind(value),
                    "value_json": exact_json(value),
                }
            )
    states: set[str] = {str(entry["state"]) for entry in observations}
    if len(states) == 1:
        field_state = str(next(iter(states)))
    elif states:
        field_state = "mixed_observations"
    else:
        field_state = "no_observations"
    return "present", field_state, observations


def _row_key_name(table: str) -> str:
    return {
        "ec_curvedata": "lmfdb_label",
        "ec_classdata": "lmfdb_iso",
        "ec_mwbsd": "lmfdb_label",
        "ec_localdata": "prime",
        "ec_galrep": "prime",
        "ec_torsion_growth": "[degree,field]",
        "ec_iwasawa": "lmfdb_label",
        "ec_padic": "p",
    }[table]


def dispatch_status(table: str, field: str) -> str:
    """Expose the producer's current source-table dispatch boundary."""
    if table not in producer.TABLE_KEYS:
        return "table_not_dispatched"
    if field in producer.JOIN_METADATA:
        return "join_metadata"
    if table == "ec_localdata":
        if field == "conductor":
            return "local_conductor_aggregation"
        return (
            "local_claim_candidate"
            if field in producer.LOCAL_PROOFS
            else "unsupported_local_field"
        )
    if table == "ec_galrep":
        return (
            "galrep_conductor_candidate"
            if field == "conductor"
            else "galrep_field_not_dispatched"
        )
    if field in producer.TABLE_FIELDS.get(table, {"conductor"}):
        return "claim_candidate"
    return "unsupported_table_field"


def producer_source(table: str, field: str, observation: dict[str, Any]) -> str:
    row_key = observation["row_key"]
    if table in {"ec_localdata", "ec_galrep"}:
        return f"{table}[{row_key}].{field}"
    if table == "ec_torsion_growth":
        degree, polynomial = row_key
        return f"{table}[degree={degree},field={canonical(polynomial)}].{field}"
    if table == "ec_padic":
        return f"{table}[{row_key}].{field}"
    return f"{table}.{field}"


def validate_producer_receipt(
    report: dict[str, Any],
    manifest: dict[str, Any],
    label: str,
    expected_input_sha256: str,
) -> None:
    receipt = report.get("input_provenance")
    if not isinstance(receipt, dict):
        raise ValueError("Producer report has no input_provenance receipt")
    expected = manifest["provenance"]
    if receipt.get("source_sha256") != expected["sha256"]:
        raise ValueError("Producer report belongs to a different native response SHA")
    if report.get("input_sha256") != expected_input_sha256:
        raise ValueError(
            "Producer report input SHA does not match exact replay projection bytes"
        )
    if receipt.get("source") != expected["source"]:
        raise ValueError("Producer report source URL does not match the native capture")
    expected_tables = [
        {
            key: entry[key]
            for key in ("name", "join_key", "join_value", "status", "row_keys")
        }
        for entry in manifest["tables"]
    ]
    if receipt.get("table_capture_manifest") != expected_tables:
        raise ValueError(
            "Producer report table receipt does not match the native capture"
        )
    curve = next(
        (entry for entry in expected_tables if entry["name"] == "ec_curvedata"), None
    )
    if curve is None or curve["join_value"] != label:
        raise ValueError("Producer receipt is not bound to the requested curve subject")


def producer_statuses(
    report: dict[str, Any] | None,
    table: str,
    field: str,
    observations: list[dict[str, Any]],
) -> tuple[str, list[dict[str, Any]]]:
    if report is None:
        return "not_run", []
    fields = report.get("fields")
    if not isinstance(fields, dict):
        raise ValueError("Producer report has no fields object")
    row_results = []
    match_count = 0
    for observation in observations:
        if observation["state"] in {"field_absent", "json_null"}:
            row_results.append(
                {
                    "row_key": observation["row_key"],
                    "status": "source_field_absent"
                    if observation["state"] == "field_absent"
                    else "source_null",
                    "reason": None,
                }
            )
            continue
        source = producer_source(table, field, observation)
        matched_row = False
        for claim_field, value in fields.items():
            if not isinstance(value, dict):
                continue
            sources = value.get("sources", [])
            if not isinstance(sources, list):
                continue
            if source in sources:
                match_count += 1
                matched_row = True
                row_results.append(
                    {
                        "row_key": observation["row_key"],
                        "source": source,
                        "claim_field": claim_field,
                        "status": value.get("status", "unknown"),
                        "reason": value.get("reason"),
                        "radius": value.get("radius"),
                    }
                )
        if not matched_row:
            row_results.append(
                {
                    "row_key": observation["row_key"],
                    "source": source,
                    "status": "not_reported",
                    "reason": None,
                }
            )
    if not match_count:
        return "not_reported", row_results
    if report.get("status") != "checked":
        return "run_rejected", row_results
    matched = [item for item in row_results if item.get("claim_field")]
    statuses = {item["status"] for item in matched}
    if any(item.get("status") == "not_reported" for item in row_results):
        return "partial_coverage", row_results
    available_count = sum(
        item["state"] not in {"field_absent", "json_null"} for item in observations
    )
    if statuses == {"checked"} and len(matched) == available_count:
        return "checked", row_results
    if statuses == {"checked"}:
        return "partial_coverage", row_results
    if len(statuses) > 1:
        return "mixed_results", row_results
    if statuses == {"partial"}:
        return "partial", row_results
    if statuses & {"unsupported", "rejected"}:
        return "unsupported", row_results
    return "reported", row_results


def consumer_status(evidence: list[dict[str, Any]]) -> str:
    if not evidence:
        return "not_sampled"
    states = {item.get("status") for item in evidence}
    assumed = bool(states & {"assumption_backed", "conditional_fixture"})
    partial = bool(states & {"partial", "bounded", "partial_fixture"}) or any(
        item.get("extent") == "partial" for item in evidence
    )
    if assumed and partial:
        return "partial_assumption_backed"
    if assumed:
        return "assumption_backed"
    if partial:
        return "partial"
    return "sampled"


def blocker_for(
    *,
    has_checker: bool,
    native_status: str,
    observations: list[dict[str, Any]],
    dispatch: str,
    producer_run: str,
    producer_result: str,
    consumer: str,
    next_step: str,
) -> dict[str, str]:
    if not has_checker:
        return {
            "layer": "checker",
            "code": "checker_route_missing",
            "detail": next_step,
        }
    if native_status == "not_captured":
        return {"layer": "native", "code": "table_not_captured", "detail": next_step}
    if native_status == "no_rows":
        return {"layer": "native", "code": "no_source_rows", "detail": next_step}
    if observations and all(row["state"] == "field_absent" for row in observations):
        return {"layer": "native", "code": "field_absent", "detail": next_step}
    if observations and all(row["state"] == "json_null" for row in observations):
        return {"layer": "native", "code": "source_null_sentinel", "detail": next_step}
    if dispatch in {
        "table_not_dispatched",
        "unsupported_table_field",
        "unsupported_local_field",
        "galrep_field_not_dispatched",
        "join_metadata",
    }:
        return {"layer": "producer_dispatch", "code": dispatch, "detail": next_step}
    if producer_run == "rejected":
        return {
            "layer": "producer",
            "code": "producer_report_rejected",
            "detail": next_step,
        }
    if producer_run == "not_supplied":
        return {
            "layer": "producer",
            "code": "producer_artifact_not_supplied",
            "detail": next_step,
        }
    if producer_result in {"not_reported", "not_run"}:
        return {
            "layer": "producer",
            "code": "source_not_reported_by_producer",
            "detail": next_step,
        }
    if producer_result in {
        "partial",
        "partial_coverage",
        "mixed_results",
        "unsupported",
        "run_rejected",
        "reported",
    }:
        return {
            "layer": "producer",
            "code": f"producer_{producer_result}",
            "detail": next_step,
        }
    if consumer == "not_sampled":
        return {
            "layer": "consumer",
            "code": "imported_consumer_missing",
            "detail": next_step,
        }
    return {
        "layer": "consumer",
        "code": "capture_bound_consumer_missing",
        "detail": "Import the certificate produced from this capture and check the typed field proof.",
    }


def build_ledger(
    native_path: Path = DEFAULT_NATIVE,
    manifest_path: Path | None = None,
    coverage_path: Path = DEFAULT_COVERAGE,
    next_steps_path: Path = DEFAULT_NEXT_STEPS,
    producer_path: Path | None = None,
) -> dict[str, Any]:
    manifest_path = manifest_path or native_path.with_suffix(".provenance.json")
    native, manifest, coverage, next_steps, replay_input_sha256 = validate_inputs(
        native_path, manifest_path, coverage_path, next_steps_path
    )
    label = manifest["label"]
    producer_report = read_json(producer_path) if producer_path else None
    if producer_report is not None:
        validate_producer_receipt(producer_report, manifest, label, replay_input_sha256)
        if producer_report.get("status") not in {"checked", "rejected"}:
            raise ValueError("Producer report has an unsupported run status")
    table_receipts = {item["name"]: item for item in manifest["tables"]}
    rows = []
    for catalog_entry in coverage["fields"]:
        table = catalog_entry["table"]
        field = catalog_entry["field"]
        key = f"{table}.{field}"
        table_status, field_status, native_rows = observations_for(
            native, table_receipts[table], field
        )
        route = dispatch_status(table, field)
        producer_result, produced = producer_statuses(
            producer_report, table, field, native_rows
        )
        evidence = [
            {**item, "binding": "same_curve_label", "capture_hash_bound": False}
            for item in catalog_entry.get("evidence", [])
            if item.get("curve") == label
        ]
        consumer = consumer_status(evidence)
        next_step = next_steps[key]
        checker_scopes = catalog_entry.get("checker_scopes", [])
        report_scopes = catalog_entry.get("report_only_scopes", [])
        blocker = blocker_for(
            has_checker=bool(checker_scopes),
            native_status=table_status,
            observations=native_rows,
            dispatch=route,
            producer_run="not_supplied"
            if producer_report is None
            else producer_report["status"],
            producer_result=producer_result,
            consumer=consumer,
            next_step=next_step,
        )
        rows.append(
            {
                "table": table,
                "field": field,
                "next_step": next_step,
                "catalogue": {
                    "status": catalog_entry.get("status"),
                    "checker_scopes": checker_scopes,
                    "report_only_scopes": report_scopes,
                    "metadata_scopes": catalog_entry.get("metadata_scopes", []),
                },
                "native": {
                    "table_status": table_status,
                    "capture_status": table_receipts[table]["status"],
                    "field_status": field_status,
                    "join_key": table_receipts[table]["join_key"],
                    "join_value": table_receipts[table]["join_value"],
                    "rows": native_rows,
                },
                "dispatch": {
                    "status": route,
                    "producer_sources": [
                        producer_source(table, field, row) for row in native_rows
                    ],
                },
                "producer": {"status": producer_result, "observations": produced},
                "consumer": {"status": consumer, "evidence": evidence},
                "publication": {"status": "not_supplied"},
                "blocker": blocker,
            }
        )

    def counts(path: tuple[str, ...]) -> dict[str, int]:
        tally = Counter()
        for entry in rows:
            current: Any = entry
            for part in path:
                current = current[part]
            tally[str(current)] += 1
        return dict(sorted(tally.items()))

    return {
        "schema": LEDGER_SCHEMA,
        "subject": label,
        "denominator": {"table_qualified_fields": 101, "distinct_names": 85},
        "provenance": manifest["provenance"],
        "inputs": {
            kind: str(path.relative_to(ROOT) if path.is_relative_to(ROOT) else path)
            if path is not None
            else None
            for kind, path in {
                "native_capture": native_path,
                "manifest": manifest_path,
                "coverage_report": coverage_path,
                "next_steps": next_steps_path,
                "producer_report": producer_path,
            }.items()
        },
        "producer_run": "not_supplied"
        if producer_report is None
        else producer_report["status"],
        "producer_obligations": producer_report.get("obligations", [])
        if producer_report
        else [],
        "producer_receipt": {
            "status": "not_supplied"
            if producer_report is None
            else "matched_sha_subject_and_table_manifest",
            "is_signature": False,
        },
        "publication_run": "not_supplied",
        "summary": {
            "catalogue_status": counts(("catalogue", "status")),
            "native_table_status": counts(("native", "table_status")),
            "native_field_status": counts(("native", "field_status")),
            "producer_dispatch": counts(("dispatch", "status")),
            "producer_status": counts(("producer", "status")),
            "consumer_status": counts(("consumer", "status")),
            "blocker": dict(
                sorted(Counter(entry["blocker"]["code"] for entry in rows).items())
            ),
        },
        "fields": rows,
    }


def atomic_write(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        staged = Path(stream.name)
        try:
            stream.write(content)
            stream.close()
            os.replace(staged, path)
        finally:
            staged.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, default=DEFAULT_NATIVE)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--next-steps", type=Path, default=DEFAULT_NEXT_STEPS)
    parser.add_argument("--producer", type=Path)
    parser.add_argument(
        "--output", type=Path, help="write atomically instead of printing JSON"
    )
    args = parser.parse_args()
    manifest = args.manifest or args.native.with_suffix(".provenance.json")
    input_paths = [args.native, manifest, args.coverage, args.next_steps]
    if args.producer:
        input_paths.append(args.producer)
    try:
        if args.output and args.output.resolve() in {
            path.resolve() for path in input_paths
        }:
            raise ValueError("Ledger output must not overwrite any input artifact")
        ledger = build_ledger(
            args.native, manifest, args.coverage, args.next_steps, args.producer
        )
        rendered = json.dumps(ledger, ensure_ascii=False, indent=2).encode() + b"\n"
        if args.output:
            atomic_write(args.output, rendered)
        else:
            print(rendered.decode(), end="")
    except (OSError, TypeError, ValueError, KeyError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
