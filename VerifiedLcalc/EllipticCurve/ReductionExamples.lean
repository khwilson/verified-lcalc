module

public import VerifiedLcalc.EllipticCurve.AdditiveExamples

@[expose] public section
namespace VerifiedLcalc.EllipticCurve.ReductionExamples
open AdditiveExamples

/-- The borderline discriminant is not accepted by the small-Delta test. -/
theorem curve32_requires_stronger_criterion :
    discriminantMinimalAt C32_a4.equation 2 = false ∧
      twoAdicC4MinimalAt C32_a4.equation 2 = true := by decide +kernel

/-- A scaled equation must not be accepted merely because its singular trace is zero. -/
theorem scaled_equation_not_accepted :
    minimalityWitness? ⟨0, 0, 0, 0, 64⟩ [2, 3] = none := by decide +kernel

/-- A true curve coefficient at an additive prime, obtained from the proved
minimal equation and Euler series, without any modularity hypothesis. -/
theorem curve32_coefficient_four : (weierstrass C32_a4.equation ℚ).LFunction 4 = 0 := by
  have h := minimal_primePower C32_a4.equation (by decide +kernel)
    (minimal_of_witness C32_a4.equation C32_a4.witness C32_a4.witness_valid)
    2 (by decide) 2
  have hc : localCoefficient (modelFactor C32_a4.equation 2).trace
      (modelFactor C32_a4.equation 2).quadratic 2 = 0 := by decide +kernel
  simpa only [show 2 ^ 2 = (4 : ℕ) by decide, hc] using h

end VerifiedLcalc.EllipticCurve.ReductionExamples
