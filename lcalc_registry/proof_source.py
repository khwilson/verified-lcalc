"""Small public consumer modules for selected, already compiled certificates."""

from collections.abc import Sequence

from .checker.contracts import Rank


def selection_source(modules: Sequence[str]) -> str:
    return "module\n\n" + "\n".join("public import " + m for m in modules) + "\n"


def usage_source(entries: Sequence[tuple[str, Rank]]) -> str:
    lines = [
        "module",
        "",
        "public import Selection",
        "",
        "@[expose] public section",
        "",
        "/-! Import Usage after checking the bundle. These named theorems reuse",
        "the compiled certificates; they do not run the numerical checker again.",
        "Analytic ranks retain the explicit ellipticModularity assumption. -/",
        "",
        "open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions",
        "",
        "namespace ImportedCertificates",
        "",
    ]
    for index, (module, rank) in enumerate(entries, 1):
        lines.extend(
            [
                f"namespace Curve{index}",
                "",
                f"-- Certificate module: {module}",
                f"abbrev equation : Artifacts.CurveEquation := {module}.result.equation",
                "",
                "theorem nonsingular : discriminant equation ≠ 0 :=",
                f"  {module}.nonsingular",
                "",
                "theorem analytic_rank :",
                "    analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ)",
                f"      = {rank} :=",
                f"  {module}.analytic_rank",
                "",
                f"end Curve{index}",
                "",
            ]
        )
    lines.extend(["end ImportedCertificates", ""])
    return "\n".join(lines)
