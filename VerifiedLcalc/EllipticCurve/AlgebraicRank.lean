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

end VerifiedLcalc.EllipticCurve
