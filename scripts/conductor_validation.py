"""Generate independently checked Lean bindings for untrusted producer metadata.
No elliptic arithmetic or rank computation is implemented in this module.
"""

from typing import Any

JsonObject = dict[str, Any]

COMPONENTS = {
    "nonsingular",
    "minimality_valid",
    "globally_minimal",
    "local_data_valid",
    "conductor_formula",
    "root_formula",
    "coefficients_correct",
    "payload_correct",
    "analytic_rank",
    "rank_lower_bound",
}
ARITHMETIC = {
    "nonsingular",
    "minimality_valid",
    "globally_minimal",
    "local_data_valid",
    "conductor_formula",
    "root_formula",
    "coefficients_correct",
}


def binding_source(
    module: str, conductor: int, cases: list[JsonObject], inputs: list[JsonObject]
) -> tuple[str, list[str]]:
    expected = {r["label"]: r for r in inputs if r["conductor"] == conductor}
    labels = [r["label"] for r in cases]
    if len(labels) != len(set(labels)) or set(labels) != set(expected):
        raise ValueError("Producer changed input labels")
    source = (
        "module\npublic import "
        + module
        + "\n@[expose] public section\nopen VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions\n"
    )
    required = []
    for row in cases:
        original = expected[row["label"]]
        ns = module + ".C" + row["label"].replace(".", "_")
        if row["namespace"] != ns or row["conductor"] != conductor:
            raise ValueError("Invalid proof namespace or conductor")
        components = row["components"]
        present = set(components)
        if (
            len(present) != len(components)
            or not present <= COMPONENTS
            or "nonsingular" not in present
        ):
            raise ValueError("Invalid component audit inventory")
        rank = row.get("proposed_rank", row.get("certified_rank"))
        lower = row.get("lower_bound")
        if rank is not None and (type(rank) is not int or rank not in [0, 1]):
            raise ValueError("Unsupported exact-rank claim")
        if lower is not None and (type(lower) is not int or lower != 1):
            raise ValueError("Unsupported lower-bound claim")
        if (
            rank is not None
            and not ARITHMETIC | {"payload_correct", "analytic_rank"} <= present
        ):
            raise ValueError("Exact-rank claim is missing mandatory component audits")
        if lower is not None and not ARITHMETIC | {"rank_lower_bound"} <= present:
            raise ValueError("Lower-bound claim is missing mandatory component audits")
        if (
            "minimality_valid" in present
            and not {"globally_minimal", "coefficients_correct"} <= present
        ):
            raise ValueError("Incomplete minimality/coefficient audit")
        if (
            "local_data_valid" in present
            and not {"conductor_formula", "root_formula"} <= present
        ):
            raise ValueError("Incomplete local-reduction audit")
        if row["status"] == "conductor-mismatch":
            raise ValueError(
                "Computed conductor disagrees with the SQL input; stop for review"
            )
        equation = (
            "{ "
            + ", ".join(
                f"{key} := {value}"
                for key, value in zip(
                    ["a1", "a2", "a3", "a4", "a6"], original["ainvs"], strict=True
                )
            )
            + " }"
        )
        source += f'\nexample : {ns}.equation = ({equation} : Artifacts.CurveEquation) ∧ {ns}.inputConductor = {conductor} ∧ {ns}.label = "{row["label"]}" := by decide +kernel\n'
        source += f"example : discriminant {ns}.equation ≠ 0 := {ns}.nonsingular\n"
        if "minimality_valid" in present:
            source += f"example : {ns}.minimality.Valid {ns}.equation := {ns}.minimality_valid\n"
        if "globally_minimal" in present:
            source += f"example : GloballyMinimalInput {ns}.equation := {ns}.globally_minimal\n"
        if "local_data_valid" in present:
            source += f"example : {ns}.localData.Valid {ns}.equation := {ns}.local_data_valid\n"
            source += f"example : wildLevel {ns}.equation {ns}.localData = {conductor} := {ns}.conductor_formula\n"
            source += f"example : wildSign {ns}.equation {ns}.localData = 1 ∨ wildSign {ns}.equation {ns}.localData = -1 := by\n  first | exact Or.inl {ns}.root_formula | exact Or.inr {ns}.root_formula\n"
        order = f"analyticOrderAt (modularWitness {ns}.equation {ns}.nonsingular).formL (1 : ℂ)"
        if lower is not None:
            source += f"example : 1 ≤ {order} := {ns}.rank_lower_bound\n"
        terms = row.get("terms")
        if rank is not None:
            bits = row.get("bits")
            if (
                type(bits) is not int
                or bits <= 0
                or type(terms) is not int
                or terms <= 0
            ):
                raise ValueError("Invalid numerical settings")
            payload = (
                "CentralPayloadCorrect" if rank == 0 else "DerivativePayloadCorrect"
            )
            source += f"example : {order} = {rank} := {ns}.analytic_rank\n"
            source += f"example : {payload} {ns}.result := {ns}.payload_correct\n"
            source += f"example : {ns}.result.equation = ({equation} : Artifacts.CurveEquation) ∧ {ns}.result.conductor = {conductor} := by decide +kernel\n"
            source += f"example : {ns}.result.policy.precisionBits = {bits} ∧ {ns}.result.termLimit = {terms} := by decide +kernel\n"
            if rank == 1:
                steps, cutoff = row.get("steps"), row.get("cutoff")
                if (
                    type(steps) is not int
                    or steps <= 0
                    or type(cutoff) is not int
                    or cutoff <= 1
                ):
                    raise ValueError("Invalid derivative grid settings")
                source += f"example : {ns}.result.stepsPerUnit = {steps} ∧ {ns}.result.cutoff = {cutoff} := by decide +kernel\n"
        if "coefficients_correct" in present:
            limit = terms if rank is not None else 8
            source += f"example : modelCoefficients {ns}.equation {limit} = (List.range {limit}).map (fun j => (weierstrass {ns}.equation ℚ).LFunction (j+1)) := {ns}.coefficients_correct\n"
        required += [ns + "." + name for name in components]
    return source, required
