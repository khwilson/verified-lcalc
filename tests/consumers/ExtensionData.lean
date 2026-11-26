/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.CanonicalHeight37
import VerifiedLcalcTests.Fixtures.ExtensionData

/-! # Consume checked field degrees, strict growth, and ordered height enclosures -/

open Lean Elab Command VerifiedLcalc ExtensionDataFixture Height37

private noncomputable def growth :=
  Growth64.certificate.torsionGrowthField.get (by rfl)

theorem imported_growth_degree : Module.finrank ℚ (AdjoinRoot growth.polynomial) = 2 :=
  growth.degree_eq.trans Growth64.torsion_growth_degree_matches

theorem imported_growth :
    letI : Fact (Irreducible growth.polynomial) := ⟨growth.irreducible⟩
    let K := AdjoinRoot growth.polynomial
    letI : DecidableEq K := Classical.decEq K
    ∃ P : (Growth64.curve.baseChange K).toAffine.Point, IsOfFinAddOrder P ∧
      ∀ Q : (Growth64.curve.baseChange ℚ).toAffine.Point,
        WeierstrassCurve.Affine.Point.map (Algebra.ofId ℚ K) Q ≠ P :=
  growth.growth

-- A single input carries both table-qualified degree and torsion fields.
example : Growth64.witness.modularDegree = some 4 := rfl
example : Growth64.certificate.modularParametrization.isNone = true := rfl
example : Growth64.witness.torsionGrowthField.map TorsionGrowthFieldClaim.degree =
    some 2 := rfl
example : Growth64.witness.torsionGrowthFactors = some [2, 2] := rfl
example : Growth64.witness.torsion = some 2 := rfl
example : Growth64.certificate.torsionGrowth.isNone = true := rfl
example : Growth64.certificate.torsion.cardinality.isNone = true := rfl

section

set_option linter.concreteInstances false

variable [Growth64Equivalence]
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
noncomputable local instance : DecidableEq K := Classical.decEq _

private noncomputable def fullGrowth :=
  FullGrowth64.certificate.torsionGrowth.get (by rfl)

example : fullGrowth.field.polynomial = f := rfl
example : fullGrowth.factors = [2, 2] := rfl
example : FullGrowth64.certificate.torsionGrowthField = some
    fullGrowth.presentation.toTorsionGrowthFieldFact := rfl
example : FullGrowth64.certificate.equationFacts.discriminant.map Subtype.val = some (-64) := rfl

theorem imported_growth_factors : List.ofFn fullGrowth.presentation.factor = [2, 2] :=
  fullGrowth.factors_eq

noncomputable def imported_growth_equivalence :
    (∀ i : Fin ([2, 2] : List ℕ).length, ZMod (([2, 2] : List ℕ).get i)) ≃+
      AddCommGroup.torsion (FullGrowth64.curve.baseChange K).toAffine.Point :=
  fullGrowth.equivalence

end

theorem imported_height :
    |(Height.generators.point ⟨0, by decide⟩).canonicalHeight -
        ((0.051111408239968840235886099757 : ℚ) : ℝ)| ≤ ((3 / 50 : ℚ) : ℝ) :=
  (Height.certificate.algebraic.heights.get (by rfl)).within_error ⟨0, by decide⟩

certify_ec LeanHeight from
  { equation := Height37.model
    generatorCoordinates := some [(0, 0)]
    canonicalHeights := some ⟨[0.051111408239968840235886099757], none⟩ }
  with_proofs { canonicalHeights := some Height37.heights }

example : LeanHeight.certificate.algebraic.heights.isSome = true := rfl

certify_ec LeanGrowth from
  { equation := ExtensionDataFixture.growthModel
    torsionGrowthField := some ⟨[1, 0, 1], 2⟩ }
  with_proofs { torsionGrowthField := some ExtensionDataFixture.growthEvidence }

example : LeanGrowth.certificate.torsionGrowthField.isSome = true := rfl

certify_ec RawReports from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0,1]],"heights":[0.051],
      "torsion_growth":{"field":[1,0,1],"degree":2}}"#

example : RawReports.certificate.algebraic.heights.isNone = true := rfl
example : RawReports.certificate.torsionGrowthField.isNone = true := rfl

-- Extension invariant factors alone cannot become a rational torsion claim.
certify_ec ExtensionFactorsOnly from_json_string
  r#"{"ainvs":[0,0,0,1,0],"torsion_growth":{"field":[1,0,1],"degree":2,"torsion":[2,2]}}"#

example : ExtensionFactorsOnly.witness.torsionGrowthFactors = some [2, 2] := rfl
example : ExtensionFactorsOnly.witness.torsion.isNone = true := rfl
example : ExtensionFactorsOnly.certificate.torsionGrowth.isNone = true := rfl

certify_ec EmptyFactors from
  { equation := ExtensionDataFixture.growthModel
    torsionGrowthField := some ⟨[1, 0, 1], 2⟩
    torsionGrowthFactors := some [] }

example : EmptyFactors.witness.torsionGrowthFactors = some [] := rfl
example : EmptyFactors.certificate.torsionGrowth.isNone = true := rfl
example : ExtensionFactorsOnly.certificate.torsion.cardinality.isNone = true := rfl
example : ExtensionFactorsOnly.certificate.torsionGrowthField.isNone = true := rfl

private meta def expectRejected (name : Name) (label : String) (command : Syntax) :
    CommandElabM Unit := do
  let messages := (← get).messages
  let errors ← try
    elabCommand command
    ((← get).messages.toList.filter (·.severity == .error)).mapM (·.data.toString)
  catch error =>
    pure [← error.toMessageData.toString]
  set { (← get) with messages }
  unless errors.any (fun message => (message.splitOn label).length > 1) do
    throwError "Expected {name} to reject {label}, got {errors}"
  for suffix in [`curve, `integral_proofs, `claimed_heights, `canonical_heights_fact,
      `claimed_torsion_growth_field, `torsion_growth_field_fact,
      `claimed_torsion_growth_factors, `torsion_growth_fact, `certificate] do
    if (← getEnv).contains (name ++ suffix) then
      throwError "Rejected report leaked {name ++ suffix}"

run_cmd do
  expectRejected `UnitFactor "torsion_growth_factors_shape" (← `(certify_ec UnitFactor
    from_json_string r#"{"ainvs":[0,0,0,1,0],"torsion_growth":{"field":[1,0,1],"degree":2,
      "torsion":[1,2]}}"#))
  expectRejected `UnorderedFactors "torsion_growth_factors_shape" (← `(certify_ec UnorderedFactors
    from_json_string r#"{"ainvs":[0,0,0,1,0],"torsion_growth":{"field":[1,0,1],"degree":2,
      "torsion":[4,2]}}"#))
  expectRejected `NoField "require a field and degree" (← `(certify_ec NoField from
    { equation := ExtensionDataFixture.growthModel, torsionGrowthFactors := some [2, 2] }))
  expectRejected `BadDegree "torsion_growth_field_shape" (← `(certify_ec BadDegree
    from_json_string r#"{"ainvs":[0,0,0,1,0],"torsion_growth":{"field":[1,0,1],"degree":4}}"#))
  expectRejected `BadLeading "torsion_growth_field_shape" (← `(certify_ec BadLeading from
    { equation := ExtensionDataFixture.growthModel, torsionGrowthField := some ⟨[1,0,0], 2⟩ }))
  expectRejected `WrongField "torsion_growth_polynomial_matches" (← `(certify_ec WrongField
    from_json_string r#"{"ainvs":[0,0,0,1,0],"torsion_growth":{"field":[-2,0,1],"degree":2}}"#
    with_proofs { torsionGrowthField := some ExtensionDataFixture.growthEvidence }))
  expectRejected `WrongHeightPoint "heights_points_match" (← `(certify_ec WrongHeightPoint
    from_json_string r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,-1,1]],"heights":[0.051]}"#
    with_proofs { canonicalHeights := some Height37.heights }))
  expectRejected `WrongInfinity "heights_points_match" (← `(certify_ec WrongInfinity
    from_json_string r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0,1]],"heights":[0]}"#
    with_proofs { canonicalHeights := some ⟨⟨1, fun _ => 0⟩,
      { reported := fun _ => 0, error := fun _ => 0,
        error_nonneg := by simp, within_error := by simp }⟩ }))
  expectRejected `WrongCenter "heights_report_matches" (← `(certify_ec WrongCenter from
    { equation := Height37.model, generatorCoordinates := some [(0, 0)],
      canonicalHeights := some ⟨[3], none⟩ }
    with_proofs { canonicalHeights := some Height37.heights }))
  expectRejected `WrongRadius "heights_report_matches" (← `(certify_ec WrongRadius
    from_json_string r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0,1]],
      "heights":[0.051111408239968840235886099757],"heights_evidence":{"errors":[0]}}"#
    with_proofs { canonicalHeights := some Height37.heights }))
  expectRejected `WrongLength "heights_shape" (← `(certify_ec WrongLength from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"gens":[[0,0,1]],"heights":[]}"#))

section

variable [Growth64Equivalence]

set_option linter.unusedSectionVars false in
set_option linter.concreteInstances false in
run_cmd do
  expectRejected `WrongFactors "torsion_growth_factors_match" (← `(certify_ec WrongFactors from
    { equation := ExtensionDataFixture.growthModel
      torsionGrowthField := some ⟨[1, 0, 1], 2⟩
      torsionGrowthFactors := some [4] }
    with_proofs { torsionGrowth := some (ExtensionDataFixture.fullEvidence inferInstance) }))

end

run_cmd do
  for name in [`ExtensionDataFixture.Growth64.certificate, `Height37.Height.certificate,
      `ExtensionDataFixture.FullGrowth64.certificate, `imported_growth_degree,
      `imported_growth, `imported_growth_factors, `imported_growth_equivalence,
      `imported_height] do
    CertifyEC.auditAxioms name
