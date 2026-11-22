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
    Module.rank ℤ (Exact.curve.baseChange ℚ).toAffine.Point = 1 := Exact.algebraic_rank

example : (0 : Cardinal) ≤ Module.rank ℤ (Partial.curve.baseChange ℚ).toAffine.Point ∧
    Module.rank ℤ (Partial.curve.baseChange ℚ).toAffine.Point ≤ 2 :=
  Partial.algebraic_rank_bounds

/-- The checked infinite-order point tightens a supplied upper bound to exact rank. -/
theorem imported_mordell_weil_rank_from_point :
    Module.rank ℤ (FromPointAndUpper.curve.baseChange ℚ).toAffine.Point = 1 :=
  FromPointAndUpper.algebraic_rank

run_cmd do
  let env ← getEnv
  if env.contains `MordellWeilRankExample.Partial.algebraic_rank then
    throwError "A two-sided interval with unequal endpoints became an exact rank"
  if env.contains `MordellWeilRankExample.Exact.analytic_rank then
    throwError "An algebraic rank became an analytic rank"
  for fact in [``imported_mordell_weil_rank, ``Partial.algebraic_rank_bounds,
      ``imported_mordell_weil_rank_from_point] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms fact) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected algebraic rank axiom in {fact}: {axiomName}"

certify_ec ReusedBounds from { equation := Exact.curve }
  with_proofs { algebraicRank := some Exact.algebraic_rank_witness }

example : (0 : Cardinal) ≤ Module.rank ℤ (ReusedBounds.curve.baseChange ℚ).toAffine.Point :=
  ReusedBounds.algebraic_rank_witness.lower_le_rank

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
