module

public import VerifiedLcalc.EllipticCurve.ReductionArithmetic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve.ReductionExamples

-- A single retained fixture exercises the special two-adic criterion.
namespace C32_a4
def equation : WeierstrassCurve ℤ := ⟨0, 0, 0, 4, 0⟩
def witness : MinimalityWitness := ⟨[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]⟩
theorem witness_valid : witness.Valid equation := by decide +kernel

theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (equation.baseChange ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel)
    (minimal_of_witness equation witness witness_valid) limit
end C32_a4


/-- The borderline discriminant is not accepted by the small-Delta test. -/
theorem curve32_requires_stronger_criterion :
    discriminantMinimalAt C32_a4.equation 2 = false ∧
      twoAdicC4MinimalAt C32_a4.equation 2 = true := by decide +kernel

/-- A scaled equation must not be accepted merely because its singular trace is zero. -/
theorem scaled_equation_not_accepted :
    minimalityWitness? ⟨0, 0, 0, 0, 64⟩ [2, 3] = none := by decide +kernel

/-- A true curve coefficient at an additive prime, obtained from the proved
minimal equation and Euler series, without any modularity hypothesis. -/
theorem curve32_coefficient_four : (WeierstrassCurve.baseChange C32_a4.equation ℚ).LFunction 4 = 0 := by
  have h := minimal_primePower C32_a4.equation (by decide +kernel)
    (minimal_of_witness C32_a4.equation C32_a4.witness C32_a4.witness_valid)
    2 (by decide) 2
  have hc : computePrimePowerCoefficient C32_a4.equation 2 2 = 0 := by decide +kernel
  simpa only [show 2 ^ 2 = (4 : ℕ) by decide, hc] using h

end VerifiedLcalc.EllipticCurve.ReductionExamples
