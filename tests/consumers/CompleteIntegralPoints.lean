/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.Curve27a3

/-! # Consume the checked complete integral-point set. -/

open VerifiedLcalc VerifiedLcalc.Examples.Curve27a3 Lean Elab Command

/-- Count distinct affine integral points even though the source lists the seed twice. -/
theorem imported_complete_integer_count : Nat.card Checked.curve.integralPoints = 2 :=
  (Checked.certificate.algebraic.completeIntegralPoints.get (by decide +kernel)).integralPoints_card

example : Checked.certificate.algebraic.completeIntegralPoints.isSome = true := by rfl
example : Checked.certificate.algebraic.regulator.isSome = true := by rfl
example :
    (Checked.certificate.algebraic.regulator.get (by decide +kernel)).exact_value.isSome = true :=
  rfl

theorem imported_regulator_value_is_one :
    ((Checked.certificate.algebraic.regulator.get (by decide +kernel)).exact_value.get
      (by decide +kernel)).val = 1 := rfl

theorem imported_regulator_eq_one :
    (Checked.curve.baseChange ℚ).toAffine.regulator = 1 := by
  let value := (Checked.certificate.algebraic.regulator.get (by decide +kernel)).exact_value.get
    (by decide +kernel)
  calc
    (Checked.curve.baseChange ℚ).toAffine.regulator = value.val := value.property
    _ = 1 := rfl

theorem imported_regulator_within_error :
    |(Checked.curve.baseChange ℚ).toAffine.regulator -
      ((Checked.certificate.algebraic.regulator.get (by decide +kernel)).reported : ℝ)| ≤
      ((Checked.certificate.algebraic.regulator.get (by decide +kernel)).error : ℝ) :=
  (Checked.certificate.algebraic.regulator.get (by decide +kernel)).within_error

certify_ec ExactRegulator from
  { equation := curve, regulator := some ⟨1, none⟩ }
  with_proofs proofs

example : ExactRegulator.certificate.algebraic.regulator.isSome = true := by rfl
example : ExactRegulator.claimed_regulator.error = none := by decide +kernel

certify_ec ApproxRegulator from
  { equation := curve, regulator := some ⟨999 / 1000, some (1 / 1000)⟩ }
  with_proofs proofs

example : ApproxRegulator.certificate.algebraic.regulator.isSome = true := by rfl

certify_ec TypedApproxRegulator from
  { equation := curve, regulator := some ⟨999 / 1000, some (1 / 1000)⟩ }
  with_proofs proofs

example : TypedApproxRegulator.certificate.algebraic.regulator.isSome = true := by rfl

certify_ec NoRankForRegulator from
  { equation := curve, regulator := some ⟨1, none⟩ }

example : NoRankForRegulator.certificate.algebraic.regulator.isNone = true := by rfl

def partialProofs : IntegralCurveProofs curve :=
  { proofs with algebraicRank := some ((proofs.algebraicRank.get (by decide +kernel)).weaken
      0 1 (by decide +kernel) (by decide +kernel)) }

certify_ec PartialRankForRegulator from
  { equation := curve, regulator := some ⟨1, none⟩ }
  with_proofs partialProofs

example : PartialRankForRegulator.certificate.algebraic.rank.isNone = true := by rfl
example : PartialRankForRegulator.certificate.algebraic.regulator.isNone = true := by rfl

private meta def expectRegulatorRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let failed ← try
    elabCommand command
    pure (← get).messages.hasErrors
  catch _ => pure true
  set { (← get) with messages }
  unless failed do throwError "Incorrect rank-zero regulator report accepted: {name}"
  for suffix in [`curve, `certificate, `regulator_value_valid, `regulator_eq_one] do
    if (← getEnv).contains (name ++ suffix) then
      throwError "Rejected regulator report leaked {name ++ suffix}"

run_cmd do
  expectRegulatorRejected `DisjointRegulator (← `(certify_ec DisjointRegulator from
    { equation := curve, regulator := some ⟨99 / 100, some 1 / 1000⟩ }
    with_proofs proofs))
  expectRegulatorRejected `NegativeRegulatorError (← `(certify_ec NegativeRegulatorError from
    { equation := curve, regulator := some ⟨1, some (-1)⟩ }
    with_proofs proofs))
example : Checked.certificate.algebraic.integralYFibers.isSome = true := by rfl
example : Checked.certificate.algebraic.rank.isSome = true := by rfl

example :
    (Checked.certificate.algebraic.completeIntegralPoints.get (by decide +kernel)).coordinates =
    ({(3, -5), (3, 4)} : Finset (ℤ × ℤ)) := by decide +kernel

example : Module.finrank ℤ (Checked.curve.baseChange ℚ).toAffine.Point = 0 :=
  Checked.certificate.algebraic.rank.get (by decide +kernel) |>.property

certify_ec ReuseSupport from
  { equation := Checked.curve, integralFiberRoots := some [(3, -5), (3, 4), (3, -5)],
    numIntegralPoints := some 2 }
  with_proofs { integralXSupport := some Checked.integral_point_certificate.support }

example : Nat.card ReuseSupport.curve.integralPoints = 2 := ReuseSupport.num_int_pts
example : ReuseSupport.listed_integral_coordinates.card ≤ 2 :=
  ReuseSupport.listed_integral_count_lower_bound

certify_ec OneSeed from
  { equation := Checked.curve, integralFiberRoots := some [(3, 4)], numIntegralPoints := some 2 }

example : OneSeed.listed_integral_coordinates.card ≤ 2 :=
  OneSeed.listed_integral_count_lower_bound
example : OneSeed.certificate.algebraic.integralYFibers.isSome = true := by rfl
example : OneSeed.certificate.algebraic.completeIntegralPoints.isNone = true := by rfl

certify_ec NoSupport from_json_string
  r#"{"ainvs":[0,0,1,0,-7],"xcoord_integral_points":[3],"num_int_pts":2}"#

example : NoSupport.listed_integral_coordinates.card = 2 := by decide +kernel
example : NoSupport.witness.numIntegralPoints = some 2 := rfl
example : NoSupport.certificate.algebraic.completeIntegralPoints.isNone = true := by rfl
example : NoSupport.certificate.algebraic.integralYFibers.isSome = true := by rfl

certify_ec DuplicateListedPoints from
  { equation := curve, integralCoordinates := some [(3, 4), (3, 4)], numIntegralPoints := some 1 }

example : DuplicateListedPoints.listed_integral_coordinates.card ≤ 1 :=
  DuplicateListedPoints.listed_integral_count_lower_bound

private meta def expectCountRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let failed ← try
    elabCommand command
    pure (← get).messages.hasErrors
  catch _ => pure true
  set { (← get) with messages }
  unless failed do throwError "Incorrect integral point count accepted: {name}"
  for suffix in [`curve, `num_int_pts, `certificate, `integral_point_certificate,
      `integral_points_complete] do
    if (← getEnv).contains (name ++ suffix) then
      throwError "Rejected integral point count leaked {name ++ suffix}"

run_cmd do
  if (← getEnv).contains `NoSupport.num_int_pts then
    throwError "A raw count without exhaustive support became a theorem"
  expectCountRejected `WrongCount (← `(certify_ec WrongCount from
    { equation := curve, integralFiberRoots := some [(3, 4)], numIntegralPoints := some 1 }
    with_proofs { integralXSupport := some integralSupport }))
  expectCountRejected `MissingSeed (← `(certify_ec MissingSeed from
    { equation := curve, integralFiberRoots := some [], numIntegralPoints := some 0 }
    with_proofs { integralXSupport := some integralSupport }))
  expectCountRejected `UndersizedWithoutSupport (← `(certify_ec UndersizedWithoutSupport from
    { equation := curve, integralCoordinates := some [(3, 4), (3, 4), (3, -5)],
      numIntegralPoints := some 1 }))
  expectCountRejected `UndersizedSeedFiber (← `(certify_ec UndersizedSeedFiber from
    { equation := curve, integralFiberRoots := some [(3, 4)], numIntegralPoints := some 1 }))
  for fact in [``imported_complete_integer_count, ``Checked.certificate, ``Checked.algebraic_rank,
      ``Checked.regulator_eq_one, ``Checked.regulator_within_error,
      ``imported_regulator_eq_one, ``imported_regulator_within_error,
      ``natCard_rational_points] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms fact) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected integral-point axiom in {fact}: {axiomName}"

private def emptyIntegralModel : WeierstrassCurve ℤ := ⟨0, 0, 1, 1, 1⟩

private def emptyIntegralSupport : IntegralXSupport emptyIntegralModel where
  xs := []
  covers x y h := by
    have he : y ^ 2 + y = x ^ 3 + x + 1 := by
      simpa [WeierstrassCurve.Affine.equation_iff, emptyIntegralModel,
        WeierstrassCurve.toAffine] using h
    have impossible : ∀ a b : ZMod 2, b ^ 2 + b ≠ a ^ 3 + a + 1 := by decide +kernel
    have hz := congrArg (Int.castRingHom (ZMod 2)) he
    apply (impossible x y ?_).elim
    simpa only [map_pow, map_add, map_one, Int.coe_castRingHom] using hz

certify_ec EmptyIntegral from
  { equation := emptyIntegralModel, integralFiberRoots := some [], numIntegralPoints := some 0 }
  with_proofs { integralXSupport := some emptyIntegralSupport }

example : Finite EmptyIntegral.curve.integralPoints ∧
    Nat.card EmptyIntegral.curve.integralPoints = 0 := by
  let facts := EmptyIntegral.certificate.algebraic.completeIntegralPoints.get (by decide +kernel)
  exact ⟨facts.finite, facts.integralPoints_card⟩
