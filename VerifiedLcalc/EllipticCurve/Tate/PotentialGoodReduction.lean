/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.PotentialGoodReductionSpec
public import TauCeti.NumberTheory.Padics.RatCast

/-! # Potential good reduction over the rational numbers

Potential good reduction at every finite place is equivalent to the reduced
denominator of the rational j-invariant being one.
-/

public section

namespace VerifiedLcalc.EllipticCurve

/-- The local integral j-invariant criterion at all primes reduces to a single
condition on the denominator of the rational j-invariant. -/
theorem hasEverywherePotentialGoodReduction_iff_j_den_eq_one (W : WeierstrassCurve ℚ)
    [W.IsElliptic] : HasEverywherePotentialGoodReduction W ↔ W.j.den = 1 := by
  rw [← Padic.forall_norm_rat_le_one_iff_den_eq_one]
  unfold HasEverywherePotentialGoodReduction
  apply forall_congr'
  intro p
  rw [WeierstrassCurve.hasPotentialGoodReduction_iff_isInteger_j]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_j]
  change (∃ z : ℤ_[p], (z : ℚ_[p]) = (W.j : ℚ_[p])) ↔
    ‖(W.j : ℚ_[p])‖ ≤ 1
  constructor
  · rintro ⟨z, hz⟩
    exact hz ▸ z.property
  · intro h
    exact ⟨⟨W.j, h⟩, rfl⟩

end VerifiedLcalc.EllipticCurve
