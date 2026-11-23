/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.MordellWeilRank

/-! # Consume a compiled algebraic rank certificate independently of analytic rank -/

open VerifiedLcalc MordellWeilRankExample Lean Elab Command

/-- The rank-one result proves the actual rank of the rational point group. -/
theorem imported_mordell_weil_rank :
    Module.finrank ℤ (Exact.curve.baseChange ℚ).toAffine.Point = 1 :=
  (Exact.certificate.algebraic.rank.get (by decide)).property

/-- The compiled public aggregate retains bounds and exact rank as typed facts. -/
example : Exact.certificate.algebraic.rankBounds.isSome := by decide
example : Exact.certificate.algebraic.rank.isSome := by decide

certify_ec RankOneRegulator from
  { equation := Exact.curve, regulator := some ⟨1, none⟩ }
  with_proofs { algebraicRank := some (Exact.certificate.algebraic.rankBounds.get (by decide)) }

example : RankOneRegulator.certificate.algebraic.rank.isSome := by decide
example : RankOneRegulator.certificate.algebraic.regulator.isNone := by decide

/-- `ngens` proves the length of the checked submitted generator list only. -/
example : Exact.certificate.algebraic.generatorCount = some 1 := by
  rfl

theorem imported_rank_certificate_summary :
    (Exact.certificate.algebraic.rankBounds.get (by decide)).lower = 1 ∧
    (Exact.certificate.algebraic.rank.get (by decide)).val = 1 ∧
    Exact.certificate.algebraic.generatorCount.get (by decide) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem imported_rank_interval_from_certificate :
    (1 : Nat) ≤ Module.finrank ℤ (Exact.curve.baseChange ℚ).toAffine.Point ∧
    Module.finrank ℤ (Exact.curve.baseChange ℚ).toAffine.Point ≤ (1 : Nat) := by
  let bounds := Exact.certificate.algebraic.rankBounds.get (by decide)
  exact ⟨bounds.lower_le_finrank, bounds.finrank_le_upper⟩

theorem imported_generator_count_from_certificate :
    (Exact.certificate.algebraic.generators.get (by decide)).1 =
      Exact.certificate.algebraic.generatorCount.get (by decide) :=
  rfl

example : (0 : Nat) ≤ Module.finrank ℤ (Partial.curve.baseChange ℚ).toAffine.Point ∧
    Module.finrank ℤ (Partial.curve.baseChange ℚ).toAffine.Point ≤ 2 :=
  Partial.algebraic_rank_bounds

example : Partial.certificate.algebraic.rankBounds.isSome := by decide
example : Partial.certificate.algebraic.rank.isNone := by decide

/-- The checked infinite-order point tightens a supplied upper bound to exact rank. -/
theorem imported_mordell_weil_rank_from_point :
    Module.finrank ℤ (FromPointAndUpper.curve.baseChange ℚ).toAffine.Point = 1 :=
  FromPointAndUpper.algebraic_rank

run_cmd do
  let env ← getEnv
  if env.contains `MordellWeilRankExample.Partial.algebraic_rank then
    throwError "A two-sided interval with unequal endpoints became an exact rank"
  if env.contains `MordellWeilRankExample.Exact.analytic_rank then
    throwError "An algebraic rank became an analytic rank"
  for fact in [``imported_mordell_weil_rank, ``imported_rank_certificate_summary,
      ``imported_rank_interval_from_certificate,
      ``imported_generator_count_from_certificate, ``Partial.algebraic_rank_bounds,
      ``imported_mordell_weil_rank_from_point] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms fact) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected algebraic rank axiom in {fact}: {axiomName}"

certify_ec ReusedBounds from { equation := Exact.curve }
  with_proofs { algebraicRank := some Exact.algebraic_rank_witness }

example : (ReusedBounds.certificate.algebraic.rankBounds.get (by decide)).lower ≤
    Module.finrank ℤ (ReusedBounds.curve.baseChange ℚ).toAffine.Point :=
  (ReusedBounds.certificate.algebraic.rankBounds.get (by decide)).lower_le_finrank

certify_ec RankClaimOnly from_json_string
  r#"{"ainvs":[0,0,0,-1,1],"rank":1,"rank_bounds":[0,2]}"#

run_cmd do
  if (← getEnv).contains `RankClaimOnly.algebraic_rank then
    throwError "Raw rank claims alone must not generate an exact theorem"
  match VerifiedLcalc.CurveDataJson.parse
      r#"{"schema":"lcalc.ec-rank.v1","ainvs":[0,0,0,-1,1],"rank":1,"parameters":{}}"# with
  | .ok w =>
    unless w.algebraicRank.isNone && w.derivativeResult.isNone do
      throwError "An incomplete legacy analytic payload was used as an algebraic claim"
  | .error err => throwError err
  match VerifiedLcalc.CurveDataJson.parse
      r#"{"ainvs":[0,0,0,-1,1],"rank":1,"coefficients":[]}"# with
  | .ok w =>
    unless w.algebraicRank == some 1 do
      throwError "A metadata key hid a native rank claim"
  | .error err => throwError err

private meta def expectRankRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let failed ← try
    elabCommand command
    pure (← get).messages.hasErrors
  catch _ => pure true
  set { (← get) with messages }
  unless failed do throwError "Incorrect rank evidence accepted: {name}"
  for suffix in [`curve, `integral_proofs, `mordell_weil_bounds, `algebraic_rank_bounds,
      `algebraic_rank_witness, `algebraic_rank_claim_consistent, `algebraic_rank_respects_points,
      `algebraic_rank_input_order, `algebraic_rank_in_input_bounds,
      `algebraic_rank_bounds_respect_points, `mordell_weil_rank, `algebraic_rank] do
    if (← getEnv).contains (name ++ suffix) then
      throwError "Rejected rank evidence leaked {name ++ suffix}"

run_cmd do
  expectRankRejected `WrongClaim (← `(certify_ec WrongClaim from
    { equation := TauCeti.WorkedExamples.curveX3SubXAddOne, algebraicRank := some 2 }
    with_proofs exactProofs))
  expectRankRejected `WrongBounds (← `(certify_ec WrongBounds from
    { equation := TauCeti.WorkedExamples.curveX3SubXAddOne, algebraicRankBounds := some (2, 3) }
    with_proofs exactProofs))
  expectRankRejected `WrongEquation (← `(certify_ec WrongEquation from
    { equation := ⟨0, 0, 0, -1, 2⟩, algebraicRank := some 1 } with_proofs exactProofs))
  expectRankRejected `RawReversedBounds (← `(certify_ec RawReversedBounds from_json_string
    r#"{"ainvs":[0,0,0,-1,1],"rank_bounds":[2,1]}"#))
  expectRankRejected `RawRankOutsideBounds (← `(certify_ec RawRankOutsideBounds from_json_string
    r#"{"ainvs":[0,0,0,-1,1],"rank":0,"rank_bounds":[1,2]}"#))
  expectRankRejected `RawRankBelowPoint (← `(certify_ec RawRankBelowPoint from
    { equation := TauCeti.WorkedExamples.curveX3SubXAddOne,
      integralCoordinates := some [(3, -5)], infiniteOrderPoints := some [0],
      algebraicRank := some 0 }))
