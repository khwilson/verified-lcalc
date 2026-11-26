"""Structural checks for the generated LMFDB dependency roadmap."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts.build_lmfdb_dependency_roadmap import build_graph  # noqa: E402


def test_graph_covers_compiled_table_qualified_catalogue_and_is_acyclic() -> None:
    graph = build_graph()
    nodes = {node["id"]: node for node in graph["nodes"]}
    fields = [node for node in nodes.values() if node["node_type"] == "field"]
    assert len(fields) == 101
    assert len({node["id"] for node in fields}) == 101
    assert sum(len(node["routes"]) for node in fields) >= 117
    assert all(node["roadmap"]["line"] > 0 for node in fields)

    adjacency = {node_id: [] for node_id in nodes}
    for edge in graph["edges"]:
        assert edge["from"] in nodes
        assert edge["to"] in nodes
        adjacency[edge["from"]].append(edge["to"])
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str) -> None:
        assert node_id not in visiting, f"cycle through {node_id}"
        if node_id in visited:
            return
        visiting.add(node_id)
        for target in adjacency[node_id]:
            visit(target)
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in nodes:
        visit(node_id)


def test_route_alternatives_and_layered_factor_chain_are_explicit() -> None:
    graph = build_graph()
    nodes = {node["id"]: node for node in graph["nodes"]}
    assert nodes["ec_mwbsd.tamagawa_product"]["wave"] == "L2"
    assert (
        nodes["ec_curvedata.regulator#route:rank-zero-exact"]["kind"]
        == "rank_zero_regulator"
    )
    assert (
        nodes["ec_curvedata.regulator#route:positive-rank-report"]["kind"]
        == "positive_rank_regulator"
    )
    positive_scope = next(
        example["scope"]
        for example in nodes["ec_curvedata.regulator"]["examples"]
        if example["kind"] == "positive_rank_regulator"
    )
    assert "accepts a positive-rank regulator report" in positive_scope
    assert "emits no checked regulator fact" in positive_scope
    assert nodes["ec_curvedata.regulator"]["consumer"]["status"] in {
        "not_sampled",
        "partial",
        "assumption_backed",
    }

    edges = graph["edges"]
    for source in ("ec_curvedata.bad_primes", "ec_localdata.tamagawa_number"):
        assert any(
            edge["from"] == source
            and edge["to"] == "ec_mwbsd.tamagawa_product"
            and edge["kind"] == "field_prerequisite"
            for edge in edges
        )
    assert any(
        edge["from"] == "ec_mwbsd.tamagawa_product"
        and edge["to"] == "ec_curvedata.sha"
        and edge["kind"] == "field_prerequisite"
        and edge.get("route")
        for edge in edges
    )
    assert any(
        edge["from"] == "ec_mwbsd.tamagawa_product" and edge["to"] == "ec_curvedata.sha"
        for edge in edges
    )
    zero_id = "ec_curvedata.regulator#route:rank-zero-exact"
    positive_id = "ec_curvedata.regulator#route:positive-rank-report"
    assert not any(edge["to"] == zero_id for edge in edges)
    assert sum(edge["to"] == positive_id for edge in edges) == 2
    assert any(
        edge["from"] == "ec_mwbsd.gens"
        and edge["to"] == "component:mordell-weil-basis-saturation"
        for edge in edges
    )
    assert not any(
        edge["from"] == "ec_mwbsd.gens" and edge["to"] == positive_id for edge in edges
    )
    assert any(
        edge["from"] == "ec_mwbsd.heights"
        and edge["to"] == "component:canonical-height-pairing-enclosure"
        for edge in edges
    )
    waves = {wave["wave"]: wave for wave in graph["waves"]}
    assert waves["BASE"]["dependency_layer"] == 0
    assert waves["L2"]["dependency_layer"] == 1
    assert waves["A2"]["dependency_layer"] == 1
    assert waves["A3"]["dependency_layer"] == 2
    assert waves["TC-31"]["dependency_layer"] == 1
    assert waves["G1"]["dependency_layer"] == 0


def test_graph_carries_native_capture_bound_producer_example_without_publication_inference() -> (
    None
):
    graph = build_graph()
    assert graph["generated_from"]["producer_example"] == (
        "docs/roadmaps/lmfdb-112-a2-producer-example.json"
    )
    fields = [node for node in graph["nodes"] if node.get("node_type") == "field"]
    assert any(node["producer"].get("status") == "checked" for node in fields)
    assert all(node["publication"].get("status") != "published" for node in fields)


def test_equivalent_catalogue_labels_keep_table_identities_and_work_package() -> None:
    graph = build_graph()
    fields = [node for node in graph["nodes"] if node["node_type"] == "field"]
    labels = [node for node in fields if node["field"] == "lmfdb_label"]
    assert len(labels) == 6
    assert len({node["table"] for node in labels}) == 6
    assert all(node["wave"] == "TC-23" for node in labels)
    classes = {
        node["table"]: node["wave"] for node in fields if node["field"] == "lmfdb_iso"
    }
    assert classes == {
        "ec_curvedata": "TC-23",
        "ec_classdata": "TC-23",
        "ec_padic": "G3",
    }
    nodes = {node["id"]: node for node in graph["nodes"]}
    for wave in graph["waves"]:
        assert nodes[wave["id"]]["dependency_layer"] == wave["dependency_layer"]


def test_stages_describe_routes_independently_of_native_sample_presence() -> None:
    nodes = {node["id"]: node for node in build_graph()["nodes"]}
    regulator = nodes["ec_curvedata.regulator"]["stages"]
    assert regulator["roadmap"]["status"] == "specified"
    assert regulator["lean"]["status"] == "scoped_checker"
    assert "rank is proved zero" in regulator["lean"]["scope"]
    assert regulator["lean"]["accepts_external_evidence"]
    assert regulator["lean"]["report_only_alternatives"]
    assert regulator["generator"]["status"] == "missing"
    squarefree = nodes["ec_curvedata.squarefree_disc"]
    assert squarefree["native"]["field_status"] == "field_absent"
    assert squarefree["stages"]["generator"]["status"] == "implemented"
    assert squarefree["stages"]["generator"]["example_status"] == "not_reported"
    for node in nodes.values():
        if node["node_type"] == "field":
            for stage in node["stages"].values():
                source = stage["source"]
                assert (
                    1
                    <= source["line"]
                    <= len((ROOT / source["path"]).read_text().splitlines())
                )
