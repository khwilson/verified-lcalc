/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.PeriodGeometry
import VerifiedLcalcTests.Fixtures.SquarePeriod
import Lean

/-! Compiled reuse of the complex period and height certificate contracts. -/

open VerifiedLcalc VerifiedLcalcTests.IsogenyClass37 VerifiedLcalcTests.PeriodGeometry37
open Lean Elab Command VerifiedLcalcTests.SquarePeriod

private noncomputable def square := Square32.certificate.periodGeometry.get (by rfl)

example : |complexPeriodArea (Square32.curve.baseChange ℚ) -
    (Square32.claimed_area.reported : ℝ)| ≤ 2 :=
  (square.area.get (by rfl)).within_error

example : |catalogueFaltingsHeight (Square32.curve.baseChange ℚ) -
    (Square32.claimed_faltings_height.reported : ℝ)| ≤ 1 :=
  (square.height.get (by rfl)).within_error

example : |catalogueStableFaltingsHeight (Square32.curve.baseChange ℚ) -
    (Square32.claimed_stable_faltings_height.reported : ℝ)| ≤ 1 :=
  (square.stableHeight.get (by rfl)).within_error

example : Square32.certificate.periodGeometry.bind PeriodGeometryFacts.ratio = none := rfl

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

example : Period37.certificate.periodGeometry.bind PeriodGeometryFacts.ratio =
    some (ratio h.complete) := rfl

example : Period37.certificate.periodGeometry.bind PeriodGeometryFacts.area = none := rfl

example : Period37.witness.area.map DecimalEnclosureClaim.reported =
    some (73381327407895767390707210033 / 10 ^ 28) := rfl

example : ∃ f, Period37.certificate.periodGeometry.bind PeriodGeometryFacts.ratio = some f ∧
    f.ratio.val = 1 := ⟨ratio h.complete, rfl, rfl⟩

example : (1 : ℝ) = complexPeriodArea (source.baseChange ℚ) /
    complexPeriodArea (source.baseChange ℚ) :=
  (ratio h.complete).ratio_eq_div

end

certify_ec ReportsOnly from ({
  equation := source
  area := some ⟨3, some (1 / 100)⟩
  faltingsHeight := some ⟨-(1 / 2), none⟩
  stableFaltingsHeight := some ⟨-(1 / 2), none⟩
  faltingsRatio := some 1 } : EllipticWitness)

example : ReportsOnly.certificate.periodGeometry = none := rfl

private meta def rejectPeriod (base : Name) (cmd : Syntax)
    (label : String) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand cmd
    failed := (← get).messages.hasErrors
  catch err =>
    let message ← err.toMessageData.toString
    unless (message.splitOn s!"failed checking {base}.{label}").length > 1 do
      throwError "Expected {base}.{label} to fail its check, got {message}"
    failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Wrong period field accepted for {base}"
  for suffix in [`curve, `witness, `period_geometry_fact, `area, `faltings_ratio, `certificate] do
    if env.contains (base ++ suffix) then
      throwError "Rejected period certificate leaked {base ++ suffix}"

run_cmd do
  rejectPeriod `WrongArea (← `(certify_ec WrongArea from
    ({ equation := squareCurve, area := some ⟨7, some 2⟩ } : EllipticWitness)
    with_proofs squareProofs)) "area"
  rejectPeriod `WrongRadius (← `(certify_ec WrongRadius from_json_string
    r#"{"ainvs":[0,0,0,-1,0],"area":6.8751858180203728274900957798,
        "area_evidence":{"error":1}}"# with_proofs squareProofs)) "area"

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

run_cmd do
  rejectPeriod `WrongRatio (← `(certify_ec WrongRatio from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"faltings_ratio":2}"# with_proofs (attachment h.complete)))
    "faltings_ratio"
  for name in [``complexPeriodArea_pos, ``complexPeriodArea_eq_of_minimal_change,
      ``FaltingsRatioFact.isGreatest_area, ``FaltingsRatioFact.ratio_eq_div,
      ``Period37.faltings_ratio, ``Period37.certificate, ``Square32.certificate,
      ``Square32.area, ``Square32.faltings_height, ``Square32.stable_faltings_height] do
    for assumption in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected period geometry axiom: {assumption}"

end
