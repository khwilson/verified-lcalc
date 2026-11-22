module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Algebraic rank certificates

Use Mathlib's `Module.rank ℤ` of the rational point group. The cardinal-valued
bound is valid without assuming finite generation; a natural-valued finrank
bound is also available when finite generation is provided. In particular,
this layer requires neither modularity nor BSD.

A family of points must be linearly independent over ℤ. Non-torsion of each
individual point does not establish independence of a family.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- An infinite-order element is an independent singleton over the integers. -/
theorem independent_singleton_of_infinite_order {G : Type*} [AddCommGroup G]
    (P : G) (hP : ¬ IsOfFinAddOrder P) :
    LinearIndependent ℤ (fun _ : Fin 1 => P) := by
  apply LinearIndependent.of_subsingleton' (0 : Fin 1)
  intro a ha
  by_contra hn
  exact hP (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, hn, ha⟩)

/-- A supplied independent family proves a lower bound on the actual point
group's ℤ-rank. The bound remains meaningful without a finite-generation axiom. -/
theorem algebraic_rank_lower_bound {W : WeierstrassCurve ℚ} {n : Nat}
    (points : Fin n → W.toAffine.Point) (h : LinearIndependent ℤ points) :
    (n : Cardinal) ≤ Module.rank ℤ W.toAffine.Point := by
  simpa using h.cardinal_le_rank

/-- Natural-valued version, with the finite-generation hypothesis explicit. -/
theorem algebraic_finrank_lower_bound {W : WeierstrassCurve ℚ}
    [Module.Finite ℤ W.toAffine.Point] {n : Nat}
    (points : Fin n → W.toAffine.Point) (h : LinearIndependent ℤ points) :
    n ≤ Module.finrank ℤ W.toAffine.Point := by
  simpa using h.fintype_card_le_finrank

/-- One infinite-order rational point proves algebraic rank at least one. -/
theorem algebraic_rank_pos_of_infinite_order {W : WeierstrassCurve ℚ}
    (P : W.toAffine.Point) (hP : ¬ IsOfFinAddOrder P) :
    (1 : Cardinal) ≤ Module.rank ℤ W.toAffine.Point :=
  algebraic_rank_lower_bound _ (independent_singleton_of_infinite_order P hP)

/-- Checked lower and upper bounds on the same curve's Mordell–Weil rank. -/
structure AlgebraicRankBounds (W : WeierstrassCurve ℚ) where
  /-- The claimed lower endpoint. -/
  lower : ℕ
  /-- The claimed upper endpoint. -/
  upper : ℕ
  /-- The actual rank is at least the lower endpoint. -/
  lower_le_rank : (lower : Cardinal) ≤ Module.rank ℤ W.toAffine.Point
  /-- The actual rank is at most the upper endpoint. -/
  rank_le_upper : Module.rank ℤ W.toAffine.Point ≤ (upper : Cardinal)

/-- A proof of exact rank gives the corresponding singleton interval. -/
def AlgebraicRankBounds.ofRankEq {W : WeierstrassCurve ℚ} (n : ℕ)
    (h : Module.rank ℤ W.toAffine.Point = (n : Cardinal)) : AlgebraicRankBounds W :=
  ⟨n, n, h.ge, h.le⟩

/-- A checked interval can prove a weaker lower and upper bound on the same curve. -/
def AlgebraicRankBounds.weaken {W : WeierstrassCurve ℚ}
    (fact : AlgebraicRankBounds W) (lower upper : ℕ)
    (hl : lower ≤ fact.lower) (hu : fact.upper ≤ upper) : AlgebraicRankBounds W :=
  ⟨lower, upper, (Nat.cast_le.mpr hl).trans fact.lower_le_rank,
    fact.rank_le_upper.trans (Nat.cast_le.mpr hu)⟩

/-- A checked additional lower bound can tighten the interval. -/
def AlgebraicRankBounds.raiseLower {W : WeierstrassCurve ℚ}
    (fact : AlgebraicRankBounds W) (lower : ℕ)
    (h : (lower : Cardinal) ≤ Module.rank ℤ W.toAffine.Point) : AlgebraicRankBounds W :=
  ⟨max fact.lower lower, fact.upper, by
    rcases le_total lower fact.lower with hl | hl
    · simpa only [max_eq_left hl] using fact.lower_le_rank
    · simpa only [max_eq_right hl] using h, fact.rank_le_upper⟩

/-- An interval with equal endpoints proves the exact Mordell–Weil rank. -/
theorem AlgebraicRankBounds.rank_eq_of_equal {W : WeierstrassCurve ℚ}
    (fact : AlgebraicRankBounds W) (h : fact.lower = fact.upper) :
    Module.rank ℤ W.toAffine.Point = (fact.lower : Cardinal) :=
  le_antisymm (by simpa only [h] using fact.rank_le_upper) fact.lower_le_rank

end VerifiedLcalc.EllipticCurve
