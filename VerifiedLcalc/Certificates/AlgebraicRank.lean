module

public import VerifiedLcalc.Certificate.Witnesses.AlgebraicRank

/-! # Natural-valued algebraic rank bounds for rational elliptic curves -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- A proof of exact natural-valued rank gives the corresponding singleton interval. -/
def AlgebraicRankBounds.ofFinrankEq {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic]
    (n : ℕ) (h : Module.finrank ℤ W.toAffine.Point = n) : AlgebraicRankBounds W :=
  ⟨n, n, h.ge, h.le⟩

/-- Compatibility constructor for existing proofs stated using `Module.rank`.
Mathlib converts any cardinal rank equal to a natural to `finrank`. -/
def AlgebraicRankBounds.ofRankEq {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic]
    (n : ℕ) (h : Module.rank ℤ W.toAffine.Point = (n : Cardinal)) :
    AlgebraicRankBounds W := by
  exact .ofFinrankEq n (Module.finrank_eq_of_rank_eq h)

/-- A checked interval can prove weaker bounds on the same curve. -/
def AlgebraicRankBounds.weaken {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic]
    (fact : AlgebraicRankBounds W) (lower upper : ℕ)
    (hl : lower ≤ fact.lower) (hu : fact.upper ≤ upper) : AlgebraicRankBounds W :=
  ⟨lower, upper, hl.trans fact.lower_le_finrank, fact.finrank_le_upper.trans hu⟩

/-- An additional checked lower bound can tighten the interval. -/
def AlgebraicRankBounds.raiseLower {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic]
    (fact : AlgebraicRankBounds W) (lower : ℕ)
    (h : lower ≤ Module.finrank ℤ W.toAffine.Point) : AlgebraicRankBounds W :=
  ⟨max fact.lower lower, fact.upper, max_le fact.lower_le_finrank h,
    fact.finrank_le_upper⟩

/-- An interval with equal endpoints proves the exact Mordell–Weil rank. -/
theorem AlgebraicRankBounds.rank_eq_of_equal {W : WeierstrassCurve ℚ}
    [W.toAffine.IsElliptic] (fact : AlgebraicRankBounds W)
    (h : fact.lower = fact.upper) : Module.finrank ℤ W.toAffine.Point = fact.lower :=
  le_antisymm (by simpa only [h] using fact.finrank_le_upper) fact.lower_le_finrank

end VerifiedLcalc.EllipticCurve
