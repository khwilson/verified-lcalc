module

public import VerifiedLcalc.Certificate.Numerical.CoefficientDefinitions

/-! Correctness lemmas for the finite prime-power coefficient table. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

theorem primePowerTable_correct (e : WeierstrassCurve ℤ) (limit : Nat)
    (f : Nat × (Nat → Int)) :
    f ∈ primePowerTable e limit ↔
      ∃ p, p ≤ limit ∧ isPrime p = true ∧ f = (p, computePrimePowerCoefficient e p) := by
  simp only [primePowerTable, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨p, ⟨hp, hi⟩, hf⟩
    exact ⟨p, by omega, hi, hf.symm⟩
  · rintro ⟨p, hp, hi, hf⟩
    exact ⟨p, ⟨by omega, hi⟩, hf.symm⟩

end VerifiedLcalc.EllipticCurve
