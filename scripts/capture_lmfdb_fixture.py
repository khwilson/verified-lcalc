"""Capture exact LMFDB joined responses and replay them for the EC producer."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import tempfile
import urllib.request
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

TABLE_KEYS = {
    "ec_curvedata": "lmfdb_label",
    "ec_classdata": "lmfdb_iso",
    "ec_mwbsd": "lmfdb_label",
    "ec_localdata": "lmfdb_label",
    "ec_galrep": "lmfdb_label",
    "ec_torsion_growth": "lmfdb_label",
    "ec_iwasawa": "lmfdb_label",
    "ec_padic": "lmfdb_iso",
}
FORMAT = "verified-lcalc-lmfdb-native-v1"


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def _object(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"Expected an object at {where}")
    return value


def _reject_constant(value: str) -> None:
    raise ValueError(f"Invalid JSON constant: {value}")


def _decode(raw: bytes, where: str) -> dict[str, Any]:
    return _object(
        json.loads(
            raw, object_pairs_hook=_unique_object, parse_constant=_reject_constant
        ),
        where,
    )


def _class_label(label: str) -> str:
    match = re.fullmatch(r"([1-9][0-9]*)\.([a-z]+)[1-9][0-9]*", label)
    if not match:
        raise ValueError(f"Invalid curve label: {label}")
    return f"{match.group(1)}.{match.group(2)}"


def _row_key(table: str, row: dict[str, Any]) -> Any:
    if table in {"ec_curvedata", "ec_classdata", "ec_mwbsd", "ec_iwasawa"}:
        return row.get(TABLE_KEYS[table])
    if table in {"ec_localdata", "ec_galrep"}:
        return row.get("prime")
    if table == "ec_torsion_growth":
        return [row.get("degree"), row.get("field")]
    if table == "ec_padic":
        return row.get("p")
    return None


def _joined_arrays(
    source: dict[str, Any],
) -> tuple[list[Any], list[Any], list[Any], list[Any], list[Any]]:
    names = source.get("tables")
    labels = source.get("labels")
    keys = source.get("label_cols")
    rowsets = source.get("data")
    totals = source.get("totals")
    if (
        not isinstance(names, list)
        or not isinstance(labels, list)
        or not isinstance(keys, list)
        or not isinstance(rowsets, list)
        or not isinstance(totals, list)
    ):
        raise ValueError(
            "Source must contain tables, labels, label_cols, data and totals arrays"
        )
    return names, labels, keys, rowsets, totals


def _table_manifest(
    source: dict[str, Any], expected_label: str | None = None
) -> tuple[str, list[dict[str, Any]]]:
    names, labels, keys, rowsets, totals = _joined_arrays(source)
    if len({len(x) for x in (names, labels, keys, rowsets, totals)}) != 1:
        raise ValueError("Joined export arrays differ in length")
    if any(not isinstance(name, str) for name in names):
        raise ValueError("Expected source table names")
    if len(names) != len(set(names)):
        raise ValueError("Repeated table in joined response")
    entries = {}
    label = None
    for table, value, key, rows, total in zip(
        names, labels, keys, rowsets, totals, strict=True
    ):
        if table not in TABLE_KEYS:
            raise ValueError(f"Unexpected table: {table}")
        if key != TABLE_KEYS[table] or not isinstance(value, str):
            raise ValueError(f"Invalid join metadata for {table}")
        if not isinstance(rows, list) or type(total) is not int or total != len(rows):
            raise ValueError(f"Truncated or inconsistent rows for {table}")
        if (
            table in {"ec_curvedata", "ec_classdata", "ec_mwbsd", "ec_iwasawa"}
            and len(rows) > 1
        ):
            raise ValueError(f"Expected at most one row in {table}")
        for i, raw_row in enumerate(rows):
            row = _object(raw_row, f"{table}[{i}]")
            if row.get(key) != value:
                raise ValueError(f"Join value mismatch in {table}[{i}]")
            if table == "ec_localdata" and (
                type(row.get("prime")) is not int or row["prime"] < 2
            ):
                raise ValueError(f"Invalid local prime in {table}[{i}]")
            if table == "ec_galrep" and (
                type(row.get("prime")) is not int
                or row["prime"] < 0
                or row["prime"] == 1
            ):
                raise ValueError(f"Invalid Galois prime in {table}[{i}]")
            if table == "ec_torsion_growth" and (
                type(row.get("degree")) is not int
                or row["degree"] < 1
                or not isinstance(row.get("field"), list)
                or len(row["field"]) != row["degree"] + 1
                or any(type(c) is not int for c in row["field"])
            ):
                raise ValueError(f"Invalid extension identity in {table}[{i}]")
            if table == "ec_padic" and (type(row.get("p")) is not int or row["p"] < 2):
                raise ValueError(f"Invalid p-adic prime in {table}[{i}]")
        if table == "ec_curvedata" and rows:
            label = rows[0].get("lmfdb_label")
        row_keys = [_row_key(table, row) for row in rows]
        if any(k is None for k in row_keys) or len(
            {json.dumps(k, sort_keys=True) for k in row_keys}
        ) != len(row_keys):
            if rows:
                raise ValueError(f"Missing or duplicate natural row key in {table}")
        entries[table] = {
            "name": table,
            "join_key": key,
            "join_value": value,
            "status": "present" if rows else "absent",
            "row_keys": row_keys,
        }
    if not isinstance(label, str):
        raise ValueError("Source contains no curve row")
    if expected_label is not None and label != expected_label:
        raise ValueError(f"LMFDB returned {label}, requested {expected_label}")
    class_label = _class_label(label)
    for entry in entries.values():
        expected_join = class_label if entry["join_key"] == "lmfdb_iso" else label
        if entry["join_value"] != expected_join:
            raise ValueError(
                f"Wrong joined subject for empty or populated {entry['name']} table"
            )
    for name, key in TABLE_KEYS.items():
        if name not in entries:
            join_value = class_label if key == "lmfdb_iso" else label
            entries[name] = {
                "name": name,
                "join_key": key,
                "join_value": join_value,
                "status": "not_captured",
                "row_keys": [],
            }
    for name, rows in zip(names, rowsets, strict=True):
        for i, row in enumerate(rows):
            if row.get("lmfdb_label") not in (None, label):
                raise ValueError(f"Curve label mismatch in {name}[{i}]")
            if row.get("lmfdb_iso") not in (None, class_label):
                raise ValueError(f"Isogeny class mismatch in {name}[{i}]")
    curve_rows = rowsets[names.index("ec_curvedata")] if "ec_curvedata" in names else []
    if len(curve_rows) != 1:
        raise ValueError("Joined response must contain exactly one curve row")
    conductor = int(class_label.split(".", 1)[0])
    class_rows = rowsets[names.index("ec_classdata")] if "ec_classdata" in names else []
    if class_rows:
        for field in ("class_size", "class_deg"):
            curve_value = curve_rows[0].get(field)
            class_value = class_rows[0].get(field)
            if (
                curve_value is not None
                and class_value is not None
                and curve_value != class_value
            ):
                raise ValueError(f"Conflicting {field} in curve and isogeny-class rows")
    for name, rows in zip(names, rowsets, strict=True):
        if any(
            r.get("conductor") is not None
            and (type(r["conductor"]) is not int or r["conductor"] != conductor)
            for r in rows
        ):
            raise ValueError(f"Conductor mismatch in {name}")
    return label, [entries[name] for name in TABLE_KEYS]


def _source_url(label: str) -> str:
    return f"https://www.lmfdb.org/EllipticCurve/Q/data/{label}?_format=json"


def _manifest(
    raw: bytes, url: str | None = None, expected_label: str | None = None
) -> dict[str, Any]:
    source = _decode(raw, "raw response")
    if "provenance" in source:
        raise ValueError("Expected a raw response without an added provenance field")
    label, tables = _table_manifest(source, expected_label)
    captured_at = source.get("timestamp")
    if not isinstance(captured_at, str) or not captured_at.strip():
        captured_at = datetime.now(UTC).isoformat()
    return {
        "format": FORMAT,
        "label": label,
        "provenance": {
            "source": url or _source_url(label),
            "source_revision": None,
            "captured_at": captured_at,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "license": "CC BY-SA",
            "attribution": "The LMFDB Collaboration",
            "payload_sha256_scope": "exact response bytes",
        },
        "tables": tables,
    }


def capture_label(label: str, timeout: int = 30) -> tuple[bytes, dict[str, Any]]:
    _class_label(label)
    request = urllib.request.Request(
        _source_url(label), headers={"User-Agent": "verified-lcalc fixture capture"}
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        raw, final_url = response.read(), response.geturl()
    return raw, _manifest(raw, final_url, label)


def replay_capture(source: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    if manifest.get("format") != FORMAT:
        raise ValueError(f"Expected manifest format {FORMAT}")
    label = manifest.get("label")
    if not isinstance(label, str):
        raise ValueError("Manifest label is missing")
    tables = manifest.get("tables")
    if not isinstance(tables, list):
        raise ValueError("Manifest tables must be a list")
    _, derived_tables = _table_manifest(source, label)
    if derived_tables != tables:
        raise ValueError(
            "Table status or natural-key manifest disagrees with raw response"
        )
    provenance = _object(manifest.get("provenance"), "manifest provenance")
    for key in ("source", "sha256", "license", "attribution", "captured_at"):
        if not isinstance(provenance.get(key), str) or not provenance[key].strip():
            raise ValueError(f"Missing provenance {key}")
    names, labels, keys, rowsets, totals = _joined_arrays(source)
    return {
        "labels": labels,
        "tables": names,
        "label_cols": keys,
        "totals": totals,
        "data": rowsets,
        "timestamp": source.get("timestamp") or provenance["captured_at"],
        "provenance": {
            "source": provenance["source"],
            "source_sha256": provenance["sha256"],
            "source_revision": provenance.get("source_revision"),
            "captured_at": provenance["captured_at"],
            "attribution": provenance["attribution"],
            "license": provenance["license"],
            "selection": "All native source tables; status, keys and exact source hash are recorded in table_capture_manifest.",
            "table_capture_manifest": tables,
        },
    }


def _inject_provenance(
    raw: bytes, source: dict[str, Any], provenance: dict[str, Any]
) -> bytes:
    """Add provenance while leaving every original JSON token byte-for-byte intact."""
    if "provenance" in source:
        raise ValueError(
            "Raw response already has provenance; refusing ambiguous replacement"
        )
    end = len(raw.rstrip())
    if end == 0 or raw[:end].rstrip()[-1:] != b"}":
        raise ValueError("Raw response is not a JSON object")
    body = raw[:end].rstrip()
    suffix = raw[end:]
    encoded_provenance = json.dumps(
        provenance, ensure_ascii=False, separators=(",", ":")
    ).encode()
    return body[:-1] + b',"provenance":' + encoded_provenance + b"}" + suffix


def _stage_bytes(destination: Path, content: bytes) -> Path:
    """Write and fsync a temporary file beside its final destination."""
    descriptor, name = tempfile.mkstemp(
        prefix=f".{destination.name}.", suffix=".stage", dir=destination.parent
    )
    staged = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        staged.unlink(missing_ok=True)
        raise
    return staged


def _install_pair_no_clobber(
    outputs: tuple[tuple[Path, bytes], tuple[Path, bytes]],
) -> None:
    """Install a raw/manifest pair without replacing existing files."""
    destinations = [path for path, _ in outputs]
    if len({path.resolve() for path in destinations}) != 2:
        raise ValueError("Raw capture and manifest outputs must be different files")
    if any(os.path.lexists(path) for path in destinations):
        raise FileExistsError(
            "Capture output pair already exists; refusing to overwrite either file"
        )
    for path in destinations:
        path.parent.mkdir(parents=True, exist_ok=True)

    staged: list[Path] = []
    installed: list[tuple[Path, tuple[int, int]]] = []
    try:
        for destination, content in outputs:
            staged.append(_stage_bytes(destination, content))
        for temporary, destination in zip(staged, destinations, strict=True):
            # link() creates the destination only if it does not exist, including
            # when another process wins the race after the preflight check.
            stat = os.stat(temporary, follow_symlinks=False)
            os.link(temporary, destination)
            installed.append((destination, (stat.st_dev, stat.st_ino)))
    except BaseException as error:
        cleanup_errors = []
        for destination, identity in reversed(installed):
            try:
                stat = os.lstat(destination)
                if (stat.st_dev, stat.st_ino) == identity:
                    os.unlink(destination)
            except FileNotFoundError:
                pass
            except OSError as cleanup_error:
                cleanup_errors.append(cleanup_error)
        if cleanup_errors:
            raise OSError(
                f"Capture pair install failed and rollback was incomplete: {cleanup_errors}"
            ) from error
        raise
    finally:
        for temporary in staged:
            temporary.unlink(missing_ok=True)


def _atomic_replace(destination: Path, content: bytes) -> None:
    """Replace one output atomically after its complete contents are staged."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    staged = _stage_bytes(destination, content)
    try:
        os.replace(staged, destination)
    finally:
        staged.unlink(missing_ok=True)


def replay_capture_bytes(raw: bytes, manifest: dict[str, Any]) -> bytes:
    """Verify exact response bytes and append the audited provenance receipt."""
    provenance = _object(manifest.get("provenance"), "manifest provenance")
    if hashlib.sha256(raw).hexdigest() != provenance.get("sha256"):
        raise ValueError("Raw source SHA-256 does not match provenance manifest")
    source = _decode(raw, "raw response")
    projection = replay_capture(source, manifest)
    return _inject_provenance(raw, source, projection["provenance"])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    capture = subs.add_parser(
        "capture", help="capture a label or exact existing response"
    )
    capture.add_argument("subject", help="LMFDB label or existing raw response file")
    capture.add_argument("--output", type=Path, required=True)
    capture.add_argument("--manifest-output", type=Path, required=True)
    replay = subs.add_parser(
        "replay", help="replay a raw capture as producer joined JSON"
    )
    replay.add_argument("capture", type=Path)
    replay.add_argument("--manifest", type=Path)
    replay.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == "capture":
            path = Path(args.subject)
            if path.is_file():
                if (
                    args.output.resolve() == path.resolve()
                    or args.manifest_output.resolve() == path.resolve()
                ):
                    raise ValueError(
                        "Capture outputs must not overwrite the source response"
                    )
                raw = path.read_bytes()
                manifest = _manifest(raw)
            else:
                raw, manifest = capture_label(args.subject)
            manifest_bytes = (
                json.dumps(manifest, ensure_ascii=False, indent=2) + "\n"
            ).encode()
            _install_pair_no_clobber(
                ((args.output, raw), (args.manifest_output, manifest_bytes))
            )
        else:
            raw = args.capture.read_bytes()
            manifest_path = args.manifest or args.capture.with_suffix(
                ".provenance.json"
            )
            if args.output.resolve() in {
                args.capture.resolve(),
                manifest_path.resolve(),
            }:
                raise ValueError(
                    "Replay output must not overwrite the raw capture or its manifest"
                )
            manifest = _decode(manifest_path.read_bytes(), "manifest")
            _atomic_replace(args.output, replay_capture_bytes(raw, manifest))
    except (OSError, ValueError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
