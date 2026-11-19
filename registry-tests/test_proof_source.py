from test_registry import witness

from lcalc_registry.checker.kernel import bindings
from lcalc_registry.proof_source import selection_source, usage_source


def test_submitted_witness_fields_have_named_public_equalities() -> None:
    payload = witness({"ainvs": ["0", "-1", "1", "-10", "-20"], "conductor": "11"})
    source = bindings("LcalcCertificates.Ctest", payload)
    assert "example :" not in source
    for theorem in [
        "subject_eq",
        "submitted_analytic_rank",
        "precision_eq",
        "coefficients_eq",
        "minimality_primes_eq",
        "local_data_eq",
        "alphaLo_eq",
        "alphaHi_eq",
        "tail_eq",
        "box_reLo_eq",
        "box_reHi_eq",
        "box_imLo_eq",
        "box_imHi_eq",
        "geometric_upper_eq",
    ]:
        assert f"theorem {theorem} :" in source
    assert "= 0 :=\n  analytic_rank" in source


def test_consumer_sources_export_named_imports_without_rechecking_numbers() -> None:
    selection = selection_source(["LcalcCertificates.Ctest"])
    usage = usage_source([("LcalcCertificates.Ctest", "1")])
    assert "public import LcalcCertificates.Ctest" in selection
    assert "public import Selection" in usage
    assert "namespace ImportedCertificates" in usage
    assert "namespace Curve1" in usage
    assert "theorem analytic_rank" in usage
    assert "  LcalcCertificates.Ctest.analytic_rank" in usage
    assert "decide" not in usage
    assert "example :" not in usage
