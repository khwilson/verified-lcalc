"""Produce and kernel-check arithmetic evidence for one rational elliptic curve."""

import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
LAKE = ["lake", "-f", "lakefile.certificates.lean", "env", "lean"]
MARKER = "EC_WITNESS_CHECK "
TABLE_KEYS = {
    "ec_curvedata": "lmfdb_label",
    "ec_classdata": "lmfdb_iso",
    "ec_mwbsd": "lmfdb_label",
    "ec_localdata": "lmfdb_label",
    "ec_galrep": "lmfdb_label",
}
PROOFS = {
    "ainvs": "nonsingular",
    "jinv": "j_invariant",
    "signD": "discriminant_sign",
    "absD": "minimal_discriminant_abs",
    "bad_primes": "bad_reduction_primes",
    "num_bad_primes": "num_bad_primes",
    "semistable": "semistable",
    "squarefree_disc": "squarefree_discriminant",
    "potential_good_reduction": "potential_good_reduction",
    "binvs": "b_invariants",
    "cinvs": "c_invariants",
    "discriminant": "discriminant",
    "j_integral": "j_integral",
    "conductor": "conductor",
    "global_root_number": "root_number",
    "aplist": "ap_correct",
    "anlist": "dirichlet_coefficients",
    "gens": "generators.points_on_curve",
    "ngens": "generators.count_valid",
    "torsion_generators": "torsion_generators.points_on_curve",
    "xcoord_integral_points": "integral_y_fiber_complete",
    "integral_points": "points_on_curve",
}
LOCAL_PROOFS = {
    "prime": "local_invariants",
    "conductor_valuation": "conductor_valuation",
    "discriminant_valuation": "local_invariants",
    "j_denominator_valuation": "local_invariants",
    "reduction_type": "local_invariants",
    "kodaira_symbol": "kodaira_symbols",
    "root_number": "local_root_numbers",
    "tamagawa_number": "tamagawa_numbers",
}
JOIN_METADATA = {"id", "lmfdb_label", "lmfdb_iso", "label", "provenance"}

TABLE_FIELDS = {
    "ec_classdata": {"aplist", "anlist", "conductor"},
    "ec_mwbsd": {
        "gens",
        "ngens",
        "torsion_generators",
        "xcoord_integral_points",
        "conductor",
    },
}
TABLE_FIELDS["ec_curvedata"] = (
    PROOFS.keys()
    - TABLE_FIELDS["ec_classdata"]
    - TABLE_FIELDS["ec_mwbsd"]
    - {"integral_points"}
) | {"conductor"}
EVIDENCE_PROOFS = {"minimality": "global_minimal", "local_data": "local_data_valid"}


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"Duplicate JSON key: {key}")
        obj[key] = value
    return obj


def invalid_constant(value: str) -> None:
    raise ValueError(f"Invalid JSON constant: {value}")


def object_value(value: Any, name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ValueError(f"Expected JSON object for {name}")
    return value


def same_value(left: Any, right: Any) -> bool:
    return json.dumps(left, sort_keys=True) == json.dumps(right, sort_keys=True)


def list_value(value: Any, name: str) -> list[Any]:
    if not isinstance(value, list):
        raise ValueError(f"Expected JSON array for {name}")
    return value


def joined_rows(
    source: dict[str, Any],
) -> tuple[list[tuple[str, dict[str, Any]]], list[dict[str, Any]]]:
    if not ({"tables", "data", "labels", "label_cols"} & source.keys()):
        return [("input", source)], source.get("local_invariants", [])
    columns = [
        list_value(source.get(key), key)
        for key in ("tables", "labels", "label_cols", "data")
    ]
    tables, labels, label_cols, rows = columns
    if len({len(column) for column in columns}) != 1:
        raise ValueError("Joined export arrays differ in length")
    if not all(isinstance(table, str) for table in tables) or len(set(tables)) != len(
        tables
    ):
        raise ValueError("Invalid or repeated joined table")
    selected = {}
    for table, label, label_col, data in zip(
        tables, labels, label_cols, rows, strict=True
    ):
        if table not in TABLE_KEYS:
            continue
        if label_col != TABLE_KEYS[table] or not isinstance(label, str) or not label:
            raise ValueError(f"Invalid join metadata for {table}")
        items = [object_value(row, table) for row in list_value(data, table)]
        if table not in {"ec_localdata", "ec_galrep"} and len(items) > 1:
            raise ValueError(f"Expected at most one row in {table}")
        if any(row.get(label_col) != label for row in items):
            raise ValueError(f"Row label disagrees with joined label for {table}")
        selected[table] = (label, items)
    if not selected.get("ec_curvedata", ("", []))[1]:
        raise ValueError("Joined export requires one ec_curvedata row")
    curve_label, [curve] = selected["ec_curvedata"]
    class_label = curve.get("lmfdb_iso")
    if (
        not isinstance(class_label, str)
        or not re.fullmatch(re.escape(class_label) + "[1-9][0-9]*", curve_label)
        or not re.fullmatch(r"[1-9][0-9]*\.[a-z]+", class_label)
    ):
        raise ValueError("Curve and isogeny-class labels disagree")
    for table, (label, items) in selected.items():
        if label != (class_label if table == "ec_classdata" else curve_label):
            raise ValueError(
                f"Joined label does not identify this curve or class in {table}"
            )
        if any("lmfdb_iso" in row and row["lmfdb_iso"] != class_label for row in items):
            raise ValueError(f"Isogeny-class label disagrees in {table}")
        if any(
            "lmfdb_label" in row and row["lmfdb_label"] != curve_label for row in items
        ):
            raise ValueError(f"Curve label disagrees in {table}")
    flat = [
        (table, row)
        for table in TABLE_FIELDS
        for row in selected.get(table, ("", []))[1]
    ]
    galrep_primes = set()
    for row in selected.get("ec_galrep", ("", []))[1]:
        prime = row.get("prime")
        if type(prime) is not int or prime < 0 or prime == 1 or prime in galrep_primes:
            raise ValueError("Invalid or repeated ec_galrep row prime")
        galrep_primes.add(prime)
        if row.get("conductor") is not None:
            flat.append((f"ec_galrep[{prime}]", {"conductor": row["conductor"]}))
    local = selected.get("ec_localdata", ("", []))[1]
    label_conductor = int(class_label.split(".", 1)[0])
    if any(
        row.get("conductor") is not None
        and not same_value(row["conductor"], label_conductor)
        for row in [*(row for _, row in flat), *local]
    ):
        raise ValueError("Joined conductor disagrees with the curve label")
    return flat, local


def build_input(
    source: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, dict[str, Any]], dict[str, list[str]]]:
    rows, local_data = joined_rows(source)
    local = [
        object_value(row, "local row")
        for row in list_value(local_data, "local_invariants")
    ]
    witness = {}
    fields = {}
    sources: dict[str, list[str]] = {}
    for table, row in rows:
        if table == "input" and EVIDENCE_PROOFS.keys() & row.keys():
            raise ValueError(
                "Supply only curve claims; the producer computes minimality and local_data"
            )
        candidates = (
            PROOFS.keys()
            if table == "input"
            else TABLE_FIELDS.get(table, {"conductor"})
        )
        for field, value in row.items():
            if field == "local_invariants" or field in JOIN_METADATA or value is None:
                continue
            if field in candidates:
                sources.setdefault(field, []).append(f"{table}.{field}")
                if field in witness and not same_value(witness[field], value):
                    raise ValueError(f"Conflicting {field} values in joined rows")
                witness[field] = value
            else:
                key = (
                    f"{table}.{field}" if field in (PROOFS | EVIDENCE_PROOFS) else field
                )
                sources.setdefault(key, []).append(f"{table}.{field}")
                fields[key] = result(
                    "unsupported", "No certificate route in this producer"
                )
    ainvs = witness.get("ainvs")
    if (
        not isinstance(ainvs, list)
        or len(ainvs) != 5
        or any(type(a) is not int for a in ainvs)
    ):
        raise ValueError("Expected five integer Weierstrass coefficients in ainvs")
    seen = set()
    local_rows = []
    local_source = "input.local_invariants" if rows[0][0] == "input" else "ec_localdata"
    for row in local:
        prime = row.get("prime")
        if type(prime) is not int or prime < 2 or prime in seen:
            raise ValueError("Invalid or repeated local row prime")
        seen.add(prime)
        if row.get("conductor") is not None:
            value = row["conductor"]
            if "conductor" in witness and not same_value(witness["conductor"], value):
                raise ValueError("Conflicting conductor values in joined rows")
            witness["conductor"] = value
            sources.setdefault("conductor", []).append(
                f"{local_source}[{prime}].conductor"
            )
        local_rows.append(
            {key: row[key] for key in LOCAL_PROOFS if row.get(key) is not None}
        )
        for field, value in row.items():
            if (
                field not in JOIN_METADATA
                and field != "conductor"
                and value is not None
            ):
                key = f"local_invariants.{prime}.{field}"
                sources[key] = [f"{local_source}[{prime}].{field}"]
                if field not in LOCAL_PROOFS:
                    fields[key] = result(
                        "unsupported", "No certificate route in this producer"
                    )
    if "conductor" in witness and (
        type(witness["conductor"]) is not int or witness["conductor"] <= 0
    ):
        raise ValueError("Expected positive integer conductor")
    if local_rows:
        witness["local_invariants"] = local_rows
    return witness, fields, sources


def result(status: str, reason: str) -> dict[str, str]:
    return {"status": status, "reason": reason}


def invoke(args: list[str]) -> str:
    process = subprocess.run(
        [*LAKE, *args], cwd=ROOT, capture_output=True, text=True, check=False
    )
    if process.returncode:
        raise ValueError(
            (process.stdout + process.stderr).strip() or "Lean exited unsuccessfully"
        )
    return process.stdout


def verifier_source(
    proofs: set[str], tamagawa: list[int], kodaira: list[tuple[int, int]]
) -> str:
    # Single backticks quote names even when optional declarations do not exist.
    names = ", ".join(f"`WitnessCheck.{name}" for name in sorted(proofs))
    primes = ", ".join(map(str, tamagawa))
    codes = ", ".join(f"({prime}, {code})" for prime, code in kodaira)
    return f"""import VerifiedLcalc.Tactic.CertifyEC

open Lean Elab Command

set_option Elab.async false

certify_ec WitnessCheck from_json "witness.json"

run_cmd do
  let env ← getEnv
  unless env.contains `WitnessCheck.certificate do
    throwError "Expected the checked certificate"
  let names : List Name := [{names}]
  let mut facts := names.map fun n => (n.toString, toJson (env.contains n))
  for p in ([{primes}] : List Nat) do
    let support ← liftTermElabM <| Lean.Meta.whnf
      (mkApp2 (mkConst ``VerifiedLcalc.EllipticCurve.supportsTamagawaOne)
        (mkConst ``WitnessCheck.curve) (mkNatLit p))
    unless support.isConstOf ``Bool.true || support.isConstOf ``Bool.false do
      throwError "Could not reduce Tamagawa support"
    facts := facts ++ [("tamagawa." ++ toString p, toJson (support.isConstOf ``Bool.true))]
  for (p, code) in ([{codes}] : List (Nat × Int)) do
    let index ← liftTermElabM <| Lean.Meta.whnf
      (mkApp (mkConst ``VerifiedLcalc.EllipticCurve.kodairaIIndex) (toExpr code))
    unless index.isAppOf ``Option.some || index.isAppOf ``Option.none do
      throwError "Could not reduce Kodaira support"
    facts := facts ++ [("kodaira." ++ toString p, toJson (index.isAppOf ``Option.some))]
  IO.println ("{MARKER}" ++ (Json.mkObj facts).compress)
"""


def checked_status(field: str, value: Any) -> dict[str, str]:
    if field in {"gens", "torsion_generators", "integral_points"} and not value:
        return result("partial", "No points supplied")
    if field in {"gens", "torsion_generators"}:
        return result(
            "partial", "Point membership only; full generation requires evidence"
        )
    if field == "xcoord_integral_points" and not value:
        return result(
            "partial", "No integral abscissas supplied; exhaustivity needs evidence"
        )
    if field == "xcoord_integral_points":
        return result(
            "partial",
            "Exact fibers over supplied abscissas; exhaustivity needs evidence",
        )
    if field in {"aplist", "anlist"} and len(value) <= int(field == "anlist"):
        return result("partial", "No positive-index coefficients supplied")
    if field in {"aplist", "anlist"}:
        return result(
            "checked", "Arithmetic L-function coefficients of the represented equation"
        )
    if field == "ngens":
        return result(
            "partial", "Exact length of the supplied list; basis evidence not supplied"
        )
    if field == "ainvs":
        return result("checked", "Given integral equation is nonsingular")
    if field in {"conductor", "global_root_number", "conductor_valuation"}:
        return result(
            "checked", "Kernel-checked using the explicit ellipticModularity assumption"
        )
    if field == "root_number":
        return result("checked", "Exact arithmetic local sign formula")
    return result("checked", "Kernel-checked certificate theorem")


def report_fields(
    witness: dict[str, Any], fields: dict[str, dict[str, Any]], flags: dict[str, bool]
) -> None:
    for field, proof in (PROOFS | EVIDENCE_PROOFS).items():
        if field in witness:
            fields[field] = (
                checked_status(field, witness[field])
                if flags.get(f"WitnessCheck.{proof}")
                else result("unsupported", "Missing evidence for the exact claim")
            )
    for row in witness.get("local_invariants", []):
        prime = row["prime"]
        for field, value in row.items():
            key = f"local_invariants.{prime}.{field}"
            if not flags.get(f"WitnessCheck.{LOCAL_PROOFS[field]}"):
                fields[key] = result(
                    "unsupported", "Missing evidence for this local claim"
                )
            elif field == "tamagawa_number" and not flags.get(f"tamagawa.{prime}"):
                fields[key] = result(
                    "unsupported",
                    "Exact Tamagawa checker requires good or I₁ reduction",
                )
            elif field == "kodaira_symbol" and not flags.get(f"kodaira.{prime}"):
                fields[key] = result(
                    "partial", "Additive family checked; exact symbol unverified"
                )
            else:
                fields[key] = checked_status(field, value)


def atomic_write(output: Path, data: bytes) -> None:
    with tempfile.NamedTemporaryFile(dir=output.parent, delete=False) as stream:
        staged = Path(stream.name)
        try:
            stream.write(data)
            stream.close()
            os.replace(staged, output)
        finally:
            staged.unlink(missing_ok=True)


def produce(source: Path, output: Path, report: dict[str, Any]) -> None:
    if source.resolve() == output.resolve() or (
        output.exists() and source.samefile(output)
    ):
        raise ValueError("Output must differ from the input")
    with source.open(encoding="utf-8") as stream:
        native = object_value(
            json.load(
                stream, object_pairs_hook=unique_object, parse_constant=invalid_constant
            ),
            "input",
        )
    witness, fields, sources = build_input(native)
    report["fields"] = fields
    if "provenance" in native:
        report["input_provenance"] = object_value(native["provenance"], "provenance")
    for field in sources:
        fields.setdefault(
            field, result("rejected", "No theorem published for this claim")
        )
        fields[field]["sources"] = list(dict.fromkeys(sources[field]))
    with tempfile.TemporaryDirectory(prefix="produce-ec-witness-") as temporary:
        work = Path(temporary)
        flat = work / "input.json"
        flat.write_text(json.dumps(witness, allow_nan=False), encoding="utf-8")
        produced = object_value(
            json.loads(
                invoke(
                    [
                        "--run",
                        str(ROOT / "benchmarks/ProduceECWitnesses.lean"),
                        "--arithmetic",
                        str(flat),
                    ]
                )
            ),
            "Lean producer result",
        )
        evidence = object_value(produced["evidence"], "Lean evidence")
        if evidence.keys() - (EVIDENCE_PROOFS.keys() | {"ap"}):
            raise ValueError("Unexpected field from Lean producer")
        obligations = list_value(produced["obligations"], "Lean obligations")
        if not all(isinstance(obligation, str) for obligation in obligations):
            raise ValueError("Expected string obligations from the Lean producer")
        report["obligations"] = obligations
        omitted_ap = 0
        if "ap" in evidence:
            if (
                "aplist_minimality_inconclusive" not in obligations
                or "aplist" not in witness
            ):
                raise ValueError("Unexpected supported aplist subset")
            native_aplist = list_value(witness.pop("aplist"), "aplist")
            supported_ap = list_value(evidence["ap"], "Lean aplist subset")
            omitted_ap = len(native_aplist) - len(supported_ap)
            if omitted_ap <= 0:
                raise ValueError("Expected a strict aplist subset")
        witness.update(evidence)
        data = (json.dumps(witness, indent=2, allow_nan=False) + "\n").encode("utf-8")
        (work / "witness.json").write_bytes(data)
        proof_names = (
            set(PROOFS.values())
            | set(LOCAL_PROOFS.values())
            | set(EVIDENCE_PROOFS.values())
        )
        tamagawa = [
            row["prime"]
            for row in witness.get("local_invariants", [])
            if "tamagawa_number" in row
        ]
        kodaira = [
            (row["prime"], int(row["kodaira_symbol"]))
            for row in witness.get("local_invariants", [])
            if "kodaira_symbol" in row
        ]
        check = work / "Check.lean"
        check.write_text(
            verifier_source(proof_names, tamagawa, kodaira), encoding="utf-8"
        )
        lines = [
            line.removeprefix(MARKER)
            for line in invoke([str(check)]).splitlines()
            if line.startswith(MARKER)
        ]
        if len(lines) != 1:
            raise ValueError("Lean did not emit the checked field report")
        flags = object_value(json.loads(lines[0]), "Lean proof report")
        report_fields(witness, fields, flags)
        if omitted_ap:
            subset_checked = witness["ap"] and flags.get("WitnessCheck.ap_correct")
            fields["aplist"] = result(
                "partial" if subset_checked else "unsupported",
                f"{omitted_ap} supplied prime coefficients lack local minimality evidence",
            )
        for name in EVIDENCE_PROOFS.keys() & witness.keys():
            fields[name]["sources"] = [f"Lean producer.{name}"]
        for field, origins in sources.items():
            fields[field]["sources"] = list(dict.fromkeys(origins))
        atomic_write(output, data)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report: dict[str, Any] = {"status": "rejected", "fields": {}, "obligations": []}
    try:
        produce(args.input, args.output, report)
    except (KeyError, OSError, TypeError, ValueError) as error:
        report["error"] = str(error)
    else:
        report["status"] = "checked"
    print(json.dumps(report, ensure_ascii=False, sort_keys=True))
    return int(report["status"] != "checked")


if __name__ == "__main__":
    raise SystemExit(main())
