import VerifiedLcalc.EllipticCurve.GlobalMinimality
import VerifiedLcalcTests.Arithmetic.ReductionExamples
import Lean

open Lean Elab Command NumberField WeierstrassCurve
open VerifiedLcalc.EllipticCurve VerifiedLcalc.EllipticCurve.ReductionExamples

-- This example requires the special c4-at-two criterion: its discriminant
-- valuation is twelve, so the small-discriminant criterion is insufficient.
local instance : (C32_a4.equation.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

example : IsGlobalMinimal (𝓞 ℚ) (C32_a4.equation.baseChange ℚ) :=
  globalMinimal_of_witness _ C32_a4.witness C32_a4.witness_valid

-- A prime outside the witness's discriminant support is also minimal.
example : IsMinimal (Localization.AtPrime (rationalPlace 3).asIdeal)
    (C32_a4.equation.baseChange ℚ) :=
  localization_minimal_of_witness _ C32_a4.witness C32_a4.witness_valid 3

-- Neither the upstream interfaces nor the new witness proofs may depend on
-- the optional modularity axiom or a localization/completion comparison axiom.
run_cmd do
  for name in [``WeierstrassCurve.isGlobalMinimal_iff,
      ``WeierstrassCurve.IsGlobalMinimal.isMinimal,
      ``WeierstrassCurve.IsGlobalMinimal.of_forall_isMinimal,
      ``IsDedekindDomain.HeightOneSpectrum.integers_valuation_localizationAtPrime,
      ``MinimalityWitness.minimalAt_of_dvd,
      ``localization_minimal_of_discriminant_not_dvd,
      ``modelMinimalAt_localization,
      ``localization_minimal_of_witness,
      ``globalMinimal_of_witness] do
    let axioms ← liftTermElabM <| Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in global minimality proof {name}: {axiomName}"
