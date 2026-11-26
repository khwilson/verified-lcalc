"""Build and audit the table-qualified LMFDB certificate dependency graph."""

from __future__ import annotations

import argparse
import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any

if __package__:
    from .report_lmfdb_field_ledger import build_ledger
else:
    from report_lmfdb_field_ledger import build_ledger

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "web/certificates/field-dependency-roadmap.json"
COVERAGE = ROOT / "web/certificates/fixture-field-coverage.json"
NEXT_STEPS = ROOT / "docs/roadmaps/lmfdb-producer-next-steps.json"
CONTRACTS = ROOT / "docs/roadmaps/lmfdb-field-contracts.json"
PRODUCER_EXAMPLE = ROOT / "docs/roadmaps/lmfdb-112-a2-producer-example.json"
SCHEMA = "lcalc.lmfdb-field-dependency-roadmap.v1"
CATALOGUE = "VerifiedLcalc/Certificate/FieldCatalogue.lean"
CATALOGUE_SYMBOL = "VerifiedLcalc.FieldCatalogue.columns"
COVERAGE_SOURCE = "tests/consumers/FixtureFieldCoverage.lean"

# These IDs are the stable workstreams named by the project roadmaps. The
# membership rules below are intentionally table-qualified at emission time;
# overlap is avoided by ordering the special table scopes before generic names.
MILESTONES: dict[str, dict[str, Any]] = {
    "BASE": {
        "title": "Existing checked routes and source metadata",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "Field inventory and supported examples",
        "dependencies": [],
    },
    "L1": {
        "title": "Canonical local reduction and potential good reduction",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "L1 · Canonical reduction and potential good reduction",
        "dependencies": [],
    },
    "L2": {
        "title": "Local Tamagawa factors and root numbers",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "L2 · Tamagawa numbers and local signs",
        "dependencies": [],
    },
    "M1": {
        "title": "Full rational torsion",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "M1 · Full rational torsion",
        "dependencies": [],
    },
    "M2": {
        "title": "Exact algebraic rank and Mordell–Weil basis",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "M2 · Exact algebraic rank and basis",
        "dependencies": [],
    },
    "M3": {
        "title": "Integral-point completeness",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "M3 · Integral-point completeness",
        "dependencies": [],
    },
    "I1": {
        "title": "Complete isogeny-class graph",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "I1 · Isogeny-class graph",
        "dependencies": [],
    },
    "I2": {
        "title": "Geometric CM and minimal quadratic twists",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "I2 · Geometric CM and minimal quadratic twists",
        "dependencies": [],
    },
    "I3": {
        "title": "Optimal quotient and Manin constant",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "I3 · Optimal quotient and Manin constant",
        "dependencies": [],
    },
    "A1": {
        "title": "Higher derivatives and analytic rank",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "A1 · Higher derivatives and rank",
        "dependencies": [],
    },
    "A2": {
        "title": "Periods, heights, and real invariants",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "A2 · Real and complex invariants",
        "dependencies": [],
    },
    "A3": {
        "title": "Analytic quotient and algebraic Sha",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "A3 · Analytic quotient and algebraic Sha",
        "dependencies": ["A1", "A2", "L2", "M1", "M2"],
    },
    "G1": {
        "title": "Galois images and Serre data",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "G1 · Galois images and Serre data",
        "dependencies": [],
    },
    "G2": {
        "title": "Torsion growth over number fields",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "G2 · Torsion growth",
        "dependencies": [],
    },
    "G3": {
        "title": "Iwasawa invariants and p-adic regulator",
        "source": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        "heading": "G3 · Iwasawa invariants and p-adic regulator",
        "dependencies": [],
    },
    "TC-23": {
        "title": "Certified conductor rosters and catalogue ordering",
        "source": "docs/TAUCETI_BACKLOG.md",
        "heading": "TC-23 · Certified conductor rosters and catalogue ordering",
        "dependencies": [],
    },
    "TC-26": {
        "title": "Complete trace fingerprint inputs",
        "source": "docs/TAUCETI_BACKLOG.md",
        "heading": "TC-26 · Complete trace fingerprint inputs",
        "dependencies": [],
    },
    "TC-31": {
        "title": "Intrinsic Serre invariants",
        "source": "docs/TAUCETI_BACKLOG.md",
        "heading": "TC-31 · Intrinsic Serre invariants",
        "dependencies": ["G1"],
    },
}

CATALOGUE_IDS = {
    "Ciso",
    "Clabel",
    "Cnumber",
    "iso_nlabel",
    "lmfdb_iso",
    "lmfdb_label",
    "lmfdb_number",
}
LOCAL_REDUCTION = {
    "prime",
    "discriminant_valuation",
    "j_denominator_valuation",
    "reduction_type",
    "conductor_valuation",
    "kodaira_symbol",
}
TORSION = {
    "torsion",
    "torsion_structure",
    "torsion_primes",
    "torsion_generators",
    "intrinsic_torsion",
}
RANK = {"gens", "ngens", "rank_bounds", "rank", "regulator", "heights"}
PERIODS = {
    "area",
    "real_period",
    "faltings_height",
    "stable_faltings_height",
    "faltings_ratio",
    "faltings_index",
    "szpiro_ratio",
    "abc_quality",
}
GALOIS = {
    "adelic_gens",
    "adelic_image",
    "adelic_level",
    "adelic_index",
    "adelic_genus",
    "elladic_image",
    "elladic_images",
    "modell_image",
    "modell_images",
    "modm_images",
    "nonmax_primes",
    "nonmax_rad",
}


def wave_for(table: str, field: str) -> str:
    if field == "lmfdb_label" or (
        field == "lmfdb_iso" and table in {"ec_curvedata", "ec_classdata"}
    ):
        return "TC-23"
    if table == "ec_localdata":
        if field in {"tamagawa_number", "root_number"}:
            return "L2"
        return "L1"
    if table == "ec_padic":
        return "G3"
    if table == "ec_torsion_growth":
        return "G2"
    if (
        table in {"ec_curvedata", "ec_classdata", "ec_galrep"}
        and field in CATALOGUE_IDS
    ):
        return "TC-23"
    if field in {"trace_hash"}:
        return "TC-26"
    if field == "serre_invariants":
        return "TC-31"
    if field in {
        "conductor",
        "semistable",
        "squarefree_disc",
        "absD",
        "bad_primes",
        "num_bad_primes",
        "potential_good_reduction",
        "discriminant_valuation",
        "j_denominator_valuation",
        "reduction_type",
        "conductor_valuation",
        "kodaira_symbol",
    }:
        return "L1"
    if field in {"tamagawa_product", "tamagawa_number", "root_number"}:
        return "L2"
    if field in TORSION:
        return "M1"
    if table == "ec_torsion_growth":
        return "G2"
    if field in {"rank", "gens", "ngens", "rank_bounds", "regulator", "heights"}:
        return "M2"
    if field in {"num_int_pts", "xcoord_integral_points"}:
        return "M3"
    if field in {"class_deg", "class_size", "isogeny_matrix", "isogeny_degrees"}:
        return "I1"
    if field in {"cm", "min_quad_twist_ainvs", "min_quad_twist_disc"}:
        return "I2"
    if field in {"degree", "manin_constant", "optimality"}:
        return "I3"
    if field == "analytic_rank":
        return "A1"
    if field in {"special_value"}:
        return "A1"
    if field in PERIODS:
        return "A2"
    if field in {"sha", "sha_primes", "sha_an"}:
        return "A3"
    if field in GALOIS:
        return "G1"
    if table == "ec_iwasawa" or table == "ec_padic":
        return "G3"
    if table == "ec_galrep" and field in {"prime", "conductor"}:
        return "G1" if field == "prime" else "L1"
    if table == "ec_classdata" and field in {"aplist", "anlist"}:
        return "BASE"
    if field in {"ainvs", "jinv", "signD"}:
        return "BASE"
    return "BASE"


def relative(path: str) -> str:
    return path.removeprefix("./")


def milestone_nodes() -> list[dict[str, Any]]:
    return [
        {
            "id": f"milestone:{name}",
            "node_type": "milestone",
            "wave": name,
            "label": item["title"],
            "status": "current" if name == "BASE" else "planned_or_partial",
            "roadmap": {
                "path": relative(item["source"]),
                "heading": item["heading"],
                "line": roadmap_line(item, name),
            },
            "dependencies": [f"milestone:{dep}" for dep in item["dependencies"]],
        }
        for name, item in MILESTONES.items()
    ]


def roadmap_line(item: dict[str, Any], wave: str) -> int:
    """Resolve a roadmap target to the source line containing its heading."""
    path = ROOT / item["source"]
    lines = path.read_text(encoding="utf-8").splitlines()
    if item["source"] == "docs/TAUCETI_BACKLOG.md":
        pattern = re.compile(rf"^##\s+{re.escape(wave)}(?:\s|—|$)")
    elif wave == "BASE":
        pattern = re.compile(r"^## Field inventory\s*$")
    else:
        pattern = re.compile(rf"^\*\*{re.escape(wave)}\s+·")
    for line_number, line in enumerate(lines, start=1):
        if pattern.search(line):
            return line_number
    raise ValueError(f"Could not resolve roadmap heading for {wave}")


def evidence_link(item: dict[str, Any], proof_source: str) -> dict[str, Any]:
    return {
        "declaration": item["theorem"],
        "source": {"path": proof_source, "line": item["proof_line"]},
        "fixture": item["source"],
        "statement": item["statement"],
        "scope": item["scope"],
        "status": item["status"],
        "extent": item["extent"],
        "value_origin": item["value_origin"],
        "assumptions": item["project_axioms"],
    }


def contract_declarations(path: dict[str, Any]) -> list[dict[str, Any]]:
    refs: list[dict[str, Any]] = []
    for role in ("claim", "output", "prerequisites", "verify"):
        for reference in path[role]:
            refs.append({**reference, "role": role})
    return refs


def route_contract(
    field_id: str,
    index: int,
    path: dict[str, Any],
    evidence: list[dict[str, Any]],
    proof_source: str,
) -> dict[str, Any]:
    route_id = f"{field_id}#route:{index}"
    return {
        "id": route_id,
        "kind": "checked" if path["verify"] else "report_only",
        "status": "catalogued",
        "json": path["json"],
        "claim": path["claim"],
        "check_id": path["check"],
        "verify": path["verify"],
        "output": path["output"],
        "prerequisites": path["prerequisites"],
        "scope": path["scope"],
        "fact": path["fact"],
        "declarations": contract_declarations(path),
        "evidence": [
            evidence_link(item, proof_source)
            for item in evidence
            if item["scope"] == path["scope"]
        ],
    }


def field_stages(
    entry: dict[str, Any],
    paths: list[dict[str, Any]],
    roadmap: dict[str, Any],
    examples: list[dict[str, Any]],
) -> dict[str, Any]:
    checked = [path for path in paths if path["verify"]]
    reports = [path["scope"] for path in paths if not path["verify"]]
    reports.extend(
        example["scope"]
        for example in examples
        if example["status"] == "report_without_checked_fact"
    )
    source = checked[0]["verify"][0] if checked else None
    if source is None:
        source = next((ref for path in paths for ref in path["claim"]), None)
    external = sorted(
        {
            ref["name"]
            for path in checked
            for ref in path["prerequisites"]
            if ref["name"].startswith("VerifiedLcalc.IntegralCurveProofs.")
        }
    )
    dispatch = entry["dispatch"]["status"]
    dispatch_sources = {
        "claim_candidate": (
            "implemented",
            "TABLE_FIELDS =",
            "Dispatches native values as claim candidates. Verification still requires the checker's hypotheses.",
        ),
        "local_claim_candidate": (
            "implemented",
            "LOCAL_PROOFS =",
            "Dispatches local claim candidates by prime. Supported reduction cases determine which checks succeed.",
        ),
        "local_conductor_aggregation": (
            "implemented",
            "LOCAL_PROOFS =",
            "Combines local exponent evidence for the conductor when coverage and checks succeed.",
        ),
        "galrep_conductor_candidate": (
            "implemented",
            'for row in selected.get("ec_galrep"',
            "Passes the curve conductor as a candidate in the Galois-representation source scope.",
        ),
        "join_metadata": (
            "metadata_only",
            "JOIN_METADATA =",
            "Uses the native value to join source records.",
        ),
    }
    generator, marker, scope = dispatch_sources.get(
        dispatch,
        (
            "missing",
            "TABLE_FIELDS =",
            "The current native producer defines no certificate dispatch for this field.",
        ),
    )
    producer_source = "scripts/produce_ec_witness.py"
    line = next(
        number
        for number, value in enumerate(
            (ROOT / producer_source).read_text(encoding="utf-8").splitlines(), 1
        )
        if value.strip().startswith(marker)
    )
    return {
        "roadmap": {
            "status": "specified",
            "scope": roadmap["heading"],
            "source": {"path": roadmap["path"], "line": roadmap["line"]},
        },
        "lean": {
            "status": "scoped_checker"
            if checked
            else "report_only"
            if reports
            else "metadata_only",
            "scope": " ".join(dict.fromkeys(path["scope"] for path in checked))
            if checked
            else " ".join(reports),
            "source": {
                "path": source["module"].replace(".", "/") + ".lean",
                "line": source["line"],
            }
            if source
            else {"path": CATALOGUE, "line": 728},
            "accepts_external_evidence": bool(external),
            "external_evidence": external,
            "report_only_alternatives": list(dict.fromkeys(reports)),
        },
        "generator": {
            "status": generator,
            "scope": scope,
            "source": {"path": producer_source, "line": line},
            "example_status": entry["producer"]["status"],
        },
    }


def field_node(
    entry: dict[str, Any], proof_source: str, contract: dict[str, Any]
) -> dict[str, Any]:
    table, field = entry["table"], entry["field"]
    field_id = f"{table}.{field}"
    catalogue = entry["catalogue"]
    evidence = entry["consumer"]["evidence"]
    paths = contract["paths"]
    routes = [
        route_contract(field_id, index, path, evidence, proof_source)
        for index, path in enumerate(paths)
    ]
    examples: list[dict[str, Any]] = []
    if field_id == "ec_curvedata.regulator":
        examples = [
            {
                "id": "ec_curvedata.regulator#rank-zero-exact",
                "kind": "rank_zero_regulator",
                "status": "checked_fixture_example",
                "source": {
                    "path": "tests/consumers/CompleteIntegralPoints.lean",
                    "line": 17,
                },
                "declarations": [
                    "CompleteIntegralPoints.imported_regulator_value_is_one",
                    "CompleteIntegralPoints.imported_regulator_eq_one",
                    "CompleteIntegralPoints.imported_regulator_within_error",
                ],
                "scope": "Rank-zero fixture with an exact regulator value; this evidence is outside the audited native-field sample count.",
            },
            {
                "id": "ec_curvedata.regulator#positive-rank-report",
                "kind": "positive_rank_regulator",
                "status": "report_without_checked_fact",
                "source": {"path": "tests/consumers/MordellWeilRank.lean", "line": 21},
                "declarations": ["MordellWeilRank.RankOneRegulator"],
                "scope": "The command accepts a positive-rank regulator report, but emits no checked regulator fact because this route lacks a saturated basis and canonical-height pairing enclosure.",
            },
        ]
        routes.extend(examples)
    actual_lean: list[dict[str, Any]] = []
    seen_refs: set[tuple[str, str, int, str]] = set()
    for index, path in enumerate(paths):
        for ref in contract_declarations(path):
            key = (ref["name"], ref["module"], ref["line"], ref["role"])
            if key not in seen_refs:
                seen_refs.add(key)
                actual_lean.append(
                    {
                        "declaration": ref["name"],
                        "module": ref["module"],
                        "line": ref["line"],
                        "role": ref["role"],
                        "route": f"{field_id}#route:{index}",
                    }
                )
    actual_lean.extend(evidence_link(item, proof_source) for item in evidence)
    wave = wave_for(table, field)
    roadmap = {
        "path": relative(MILESTONES[wave]["source"]),
        "heading": MILESTONES[wave]["heading"],
        "line": roadmap_line(MILESTONES[wave], wave),
    }
    return {
        "id": field_id,
        "node_type": "field",
        "table": table,
        "field": field,
        "label": field,
        "wave": wave,
        "roadmap": roadmap,
        "stages": field_stages(entry, paths, roadmap, examples),
        "status": catalogue["status"],
        "actualLean": actual_lean,
        "catalogueLink": {
            "path": CATALOGUE,
            "declaration": CATALOGUE_SYMBOL,
            "line": 728,
            "role": "audited table-to-route catalogue; this is not a per-field proof claim",
        },
        "routes": routes,
        "examples": examples,
        "checkerScopes": catalogue["checker_scopes"],
        "reportOnlyScopes": catalogue["report_only_scopes"],
        "metadataScopes": catalogue["metadata_scopes"],
        "nextStep": entry["next_step"],
        "native": entry["native"],
        "producerDispatch": entry["dispatch"],
        "producer": entry["producer"],
        "consumer": entry["consumer"],
        "publication": entry["publication"],
        "blocker": entry["blocker"],
    }


def build_graph() -> dict[str, Any]:
    ledger = build_ledger(producer_path=PRODUCER_EXAMPLE)
    coverage = json.loads(COVERAGE.read_text(encoding="utf-8"))
    contracts = json.loads(CONTRACTS.read_text(encoding="utf-8"))
    contract_map = {f"{entry['table']}.{entry['field']}": entry for entry in contracts}
    nodes = milestone_nodes()
    fields = sorted(ledger["fields"], key=lambda item: (item["table"], item["field"]))
    field_ids = {f"{row['table']}.{row['field']}" for row in fields}
    if len(fields) != 101 or len(field_ids) != 101:
        raise ValueError("The audited table-qualified field denominator must be 101")
    if set(contract_map) != field_ids or len(contracts) != 101:
        raise ValueError(
            "Compiled field contracts must cover exactly the 101 catalogue entries"
        )
    field_nodes = [
        field_node(
            entry,
            coverage["proof_source"],
            contract_map[f"{entry['table']}.{entry['field']}"],
        )
        for entry in fields
    ]
    nodes.extend(field_nodes)
    field_route_ids = {
        field_node["id"]: [
            route["id"]
            for route in field_node["routes"]
            if route.get("kind") == "checked"
        ]
        for field_node in field_nodes
    }

    edges: list[dict[str, str]] = []
    for name, item in MILESTONES.items():
        target = f"milestone:{name}"
        for dependency in item["dependencies"]:
            edges.append(
                {
                    "from": f"milestone:{dependency}",
                    "to": target,
                    "kind": "roadmap_prerequisite",
                    "reason": f"{name} roadmap work depends on {dependency} workstream.",
                }
            )
    for entry in fields:
        wave = wave_for(entry["table"], entry["field"])
        edges.append(
            {
                "from": f"milestone:{wave}",
                "to": f"{entry['table']}.{entry['field']}",
                "kind": "workstream_scope",
                "reason": f"This table-qualified field is assigned to the {wave} roadmap target.",
            }
        )
    declaration_map: dict[str, dict[str, Any]] = {}
    for contract in contracts:
        field_id = f"{contract['table']}.{contract['field']}"
        for index, path in enumerate(contract["paths"]):
            route_id = f"{field_id}#route:{index}"
            nodes.append(
                {
                    "id": route_id,
                    "node_type": "route",
                    "field_id": field_id,
                    "route_index": index,
                    "label": path["scope"],
                    "kind": "checked" if path["verify"] else "report_only",
                    "scope": path["scope"],
                    "json": path["json"],
                }
            )
            for role in ("claim", "output", "prerequisites", "verify"):
                for reference in path[role]:
                    declaration = reference["name"]
                    node_id = f"lean:{declaration}"
                    descriptor = {
                        "id": node_id,
                        "node_type": "lean_declaration",
                        "label": declaration,
                        "declaration": declaration,
                        "module": reference["module"],
                        "line": reference["line"],
                    }
                    previous = declaration_map.get(declaration)
                    if previous and (previous["module"], previous["line"]) != (
                        reference["module"],
                        reference["line"],
                    ):
                        raise ValueError(
                            f"Conflicting compiled source locations for {declaration}"
                        )
                    declaration_map[declaration] = descriptor
                    edge_kind = {
                        "prerequisites": "lean_prerequisite",
                        "verify": "verification_handler",
                        "claim": "typed_input",
                        "output": "typed_output",
                    }[role]
                    if role == "claim":
                        edges.append(
                            {
                                "from": node_id,
                                "to": route_id,
                                "kind": edge_kind,
                                "reason": f"{declaration} is the typed input claim for this route.",
                            }
                        )
                    elif role != "output":
                        edges.append(
                            {
                                "from": node_id,
                                "to": route_id,
                                "kind": edge_kind,
                                "reason": f"{declaration} is recorded as this route's {role} declaration.",
                            }
                        )
            edges.append(
                {
                    "from": route_id,
                    "to": field_id,
                    "kind": "route_scope",
                    "reason": "This compiled route interprets or reports the table-qualified field.",
                }
            )
    nodes.extend(declaration_map.values())
    # These are field-specific mathematical prerequisites. The route node
    # qualifies the dependency so unrelated fields in the same roadmap wave
    # do not inherit it.
    for source in ("ec_curvedata.bad_primes", "ec_localdata.tamagawa_number"):
        for target_route in field_route_ids.get("ec_mwbsd.tamagawa_product", []):
            edges.append(
                {
                    "from": source,
                    "to": target_route,
                    "kind": "local_factor_input",
                    "reason": "The global Tamagawa product uses the complete bad-prime roster and each local Tamagawa factor.",
                }
            )
        edges.append(
            {
                "from": source,
                "to": "ec_mwbsd.tamagawa_product",
                "kind": "field_prerequisite",
                "reason": "The global Tamagawa product uses the complete bad-prime roster and each local Tamagawa factor.",
                "route": field_route_ids.get("ec_mwbsd.tamagawa_product", [None])[0]
                or "",
            }
        )
    sha_factor_sources = (
        "ec_mwbsd.special_value",
        "ec_mwbsd.real_period",
        "ec_mwbsd.tamagawa_product",
        "ec_curvedata.regulator",
        "ec_curvedata.torsion",
    )
    for target in ("ec_curvedata.sha", "ec_mwbsd.sha_an"):
        for target_route in field_route_ids.get(target, []):
            for source in sha_factor_sources:
                edges.append(
                    {
                        "from": source,
                        "to": target_route,
                        "kind": "bsd_quotient_factor",
                        "reason": "This analytic Sha quotient route uses the named BSD formula factor as an input.",
                    }
                )
                edges.append(
                    {
                        "from": source,
                        "to": target,
                        "kind": "field_prerequisite",
                        "reason": "This analytic Sha quotient uses the named BSD formula factor as an input.",
                        "route": target_route,
                    }
                )
    for field_id in ("ec_curvedata.faltings_index", "ec_curvedata.faltings_ratio"):
        for target_route in field_route_ids.get(field_id, []):
            edges.append(
                {
                    "from": "ec_classdata.class_size",
                    "to": target_route,
                    "kind": "class_relative_scope",
                    "reason": "This field is class-relative and requires the complete isogeny-class data route.",
                }
            )
            edges.append(
                {
                    "from": "ec_classdata.class_size",
                    "to": field_id,
                    "kind": "field_prerequisite",
                    "reason": "This field is class-relative and requires the complete isogeny-class data route.",
                    "route": target_route,
                }
            )
    # Positive-rank regulator evidence depends on a basis/saturation route
    # and height data. The rank-zero exact example above is independent.
    nodes.extend(
        [
            {
                "id": "ec_curvedata.regulator#route:rank-zero-exact",
                "node_type": "route_example",
                "field_id": "ec_curvedata.regulator",
                "kind": "rank_zero_regulator",
                "label": "Rank-zero exact regulator example",
            },
            {
                "id": "ec_curvedata.regulator#route:positive-rank-report",
                "node_type": "route_example",
                "field_id": "ec_curvedata.regulator",
                "kind": "positive_rank_regulator",
                "label": "Positive-rank report-only route",
            },
        ]
    )
    nodes.extend(
        [
            {
                "id": "component:mordell-weil-basis-saturation",
                "node_type": "missing_component",
                "field_id": "ec_curvedata.regulator",
                "label": "Saturated Mordell–Weil basis",
                "status": "missing_checked_component",
            },
            {
                "id": "component:canonical-height-pairing-enclosure",
                "node_type": "missing_component",
                "field_id": "ec_curvedata.regulator",
                "label": "Canonical height and pairing enclosure",
                "status": "missing_checked_component",
            },
        ]
    )
    edges.extend(
        [
            {
                "from": "ec_mwbsd.gens",
                "to": "component:mordell-weil-basis-saturation",
                "kind": "basis_membership_input",
                "reason": "Submitted generator membership is needed to establish the candidate Mordell–Weil basis.",
            },
            {
                "from": "component:mordell-weil-basis-saturation",
                "to": "ec_curvedata.regulator#route:positive-rank-report",
                "kind": "positive_rank_regulator_prerequisite",
                "reason": "A positive-rank regulator requires a saturated Mordell–Weil basis.",
            },
            {
                "from": "ec_mwbsd.heights",
                "to": "component:canonical-height-pairing-enclosure",
                "kind": "height_observation_input",
                "reason": "Native height observations need a checked canonical-height and pairing enclosure.",
            },
            {
                "from": "component:canonical-height-pairing-enclosure",
                "to": "ec_curvedata.regulator#route:positive-rank-report",
                "kind": "positive_rank_regulator_prerequisite",
                "reason": "A positive-rank regulator requires a certified canonical-height pairing determinant.",
            },
        ]
    )
    dependencies = [
        {
            "id": f"milestone:{name}",
            "depends_on": [f"milestone:{dep}" for dep in item["dependencies"]],
        }
        for name, item in MILESTONES.items()
    ]
    # Numbered layers are computed from hard prerequisite edges only. Work
    # assignment IDs remain the roadmap's stable L1/G3/etc identifiers.
    hard_kinds = {
        "roadmap_prerequisite",
        "lean_prerequisite",
        "verification_handler",
        "typed_input",
        "local_factor_input",
        "field_prerequisite",
        "bsd_quotient_factor",
        "class_relative_scope",
        "positive_rank_regulator_prerequisite",
        "basis_membership_input",
        "height_observation_input",
    }
    layer_by_id = dependency_layers(nodes, edges, hard_kinds)
    dependency_layers(nodes, edges, {edge["kind"] for edge in edges})
    for node in nodes:
        node["dependency_layer"] = layer_by_id[node["id"]]
    wave_data = [node for node in nodes if node["node_type"] == "milestone"]
    for milestone in wave_data:
        assigned_fields = [
            node for node in field_nodes if node["wave"] == milestone["wave"]
        ]
        milestone["dependency_layer"] = max(
            milestone["dependency_layer"],
            *(layer_by_id[node["id"]] for node in assigned_fields),
        )
        milestone["field_ids"] = [node["id"] for node in assigned_fields]
        milestone["field_count"] = len(assigned_fields)
    return {
        "schema": SCHEMA,
        "generated_from": {
            "coverage": relative(str(COVERAGE.relative_to(ROOT))),
            "proof_source": coverage["proof_source"],
            "catalogue": CATALOGUE,
            "catalogue_declaration": CATALOGUE_SYMBOL,
            "compiled_contracts": "docs/roadmaps/lmfdb-field-contracts.json",
            "producer_example": "docs/roadmaps/lmfdb-112-a2-producer-example.json",
            "next_steps": "docs/roadmaps/lmfdb-producer-next-steps.json",
            "ledger_schema": ledger["schema"],
            "native_subject": ledger["subject"],
            "native_sha256": ledger["provenance"]["sha256"],
            "native_capture": ledger["inputs"]["native_capture"],
            "native_manifest": ledger["inputs"]["manifest"],
            "mathlib_revision": "31ce06eaadf4a200c0e1407c5f10953cf606b8f8",
            "tauceti_revision": "e0e414ce57522ba17560057ad0d7f2edab91bf0c",
            "wave_specification": "docs/roadmaps/LMFDB_Q_CERTIFICATION.md",
        },
        "git_revision": coverage.get("git_revision"),
        "denominator": ledger["denominator"],
        "waves": wave_data,
        "milestone_dependencies": dependencies,
        "scheduling_edges": [
            {
                "from": "milestone:M1",
                "to": "milestone:M2",
                "reason": "Implementation order only; not a mathematical prerequisite.",
            },
            {
                "from": "milestone:M2",
                "to": "milestone:M3",
                "reason": "Implementation order only; not a mathematical prerequisite.",
            },
        ],
        "nodes": nodes,
        "edges": edges,
        "summary": ledger["summary"],
    }


def render(graph: dict[str, Any]) -> bytes:
    return (json.dumps(graph, ensure_ascii=False, indent=2) + "\n").encode()


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        staged = Path(stream.name)
        try:
            stream.write(data)
            stream.close()
            os.chmod(staged, 0o644)
            os.replace(staged, path)
        finally:
            staged.unlink(missing_ok=True)


def dependency_layers(
    nodes: list[dict[str, Any]], edges: list[dict[str, str]], hard_kinds: set[str]
) -> dict[str, int]:
    node_ids = [node["id"] for node in nodes]
    if len(node_ids) != len(set(node_ids)):
        raise ValueError("Dependency graph contains duplicate node IDs")
    known = set(node_ids)
    adjacency: dict[str, list[str]] = {node_id: [] for node_id in node_ids}
    indegree = dict.fromkeys(node_ids, 0)
    for edge in edges:
        if edge["from"] not in known or edge["to"] not in known:
            raise ValueError(f"Dependency edge references unknown node: {edge}")
        if edge["kind"] not in hard_kinds:
            continue
        adjacency[edge["from"]].append(edge["to"])
        indegree[edge["to"]] += 1
    ready = [node_id for node_id, degree in indegree.items() if degree == 0]
    layers = dict.fromkeys(node_ids, 0)
    visited = 0
    while ready:
        source = ready.pop()
        visited += 1
        for target in adjacency[source]:
            layers[target] = max(layers[target], layers[source] + 1)
            indegree[target] -= 1
            if indegree[target] == 0:
                ready.append(target)
    if visited != len(node_ids):
        cyclic = sorted(node_id for node_id, degree in indegree.items() if degree)
        raise ValueError(f"Hard prerequisite graph contains a cycle: {cyclic[:8]}")
    return layers


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write", action="store_true", help="write the generated graph"
    )
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    graph = build_graph()
    data = render(graph)
    if args.write:
        atomic_write(args.output, data)
        return 0
    if not args.output.exists() or args.output.read_bytes() != data:
        parser.error(f"{args.output} is stale; regenerate with --write")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
