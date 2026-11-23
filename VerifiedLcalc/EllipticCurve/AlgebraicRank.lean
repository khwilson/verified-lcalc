module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.GroupTheory.OrderOfElement
public import VerifiedLcalc.Certificate.Support.AlgebraicRank
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-!
# Algebraic rank certificates

Use Mathlib's `Module.finrank ℤ` of the rational point group. TauCeti proves
Mordell–Weil finite generation for every nonsingular rational elliptic curve,
so this natural number is the actual Mordell–Weil rank. This layer requires
neither modularity nor BSD.

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

/-- Compatibility form of the independent-family bound, valid without
assuming finite generation. Elliptic-curve certificates use the natural form
`algebraic_rank_lower_bound` below. -/
theorem algebraic_cardinal_rank_lower_bound {W : WeierstrassCurve ℚ} {n : Nat}
    (points : Fin n → W.toAffine.Point) (h : LinearIndependent ℤ points) :
    (n : Cardinal) ≤ Module.rank ℤ W.toAffine.Point := by
  simpa using h.cardinal_le_rank

/-- Natural-valued form of the independent-family bound for any finite module. -/
theorem algebraic_finrank_lower_bound {W : WeierstrassCurve ℚ}
    [Module.Finite ℤ W.toAffine.Point] {n : Nat}
    (points : Fin n → W.toAffine.Point) (h : LinearIndependent ℤ points) :
    n ≤ Module.finrank ℤ W.toAffine.Point := by
  simpa using h.fintype_card_le_finrank

/-- A supplied independent family proves a lower bound for the Mordell–Weil
rank of a nonsingular rational elliptic curve. -/
theorem algebraic_rank_lower_bound {W : WeierstrassCurve ℚ} [W.toAffine.IsElliptic]
    {n : Nat} (points : Fin n → W.toAffine.Point) (h : LinearIndependent ℤ points) :
    n ≤ Module.finrank ℤ W.toAffine.Point := by
  classical
  exact algebraic_finrank_lower_bound points h

/-- One infinite-order rational point proves algebraic rank at least one. -/
theorem algebraic_rank_pos_of_infinite_order {W : WeierstrassCurve ℚ}
    [W.toAffine.IsElliptic] (P : W.toAffine.Point) (hP : ¬ IsOfFinAddOrder P) :
    1 ≤ Module.finrank ℤ W.toAffine.Point :=
  algebraic_rank_lower_bound _ (independent_singleton_of_infinite_order P hP)

/-- Cardinal-valued compatibility consequence for callers that do not need
a finite rank certificate. -/
theorem algebraic_cardinal_rank_pos_of_infinite_order {W : WeierstrassCurve ℚ}
    (P : W.toAffine.Point) (hP : ¬ IsOfFinAddOrder P) :
    (1 : Cardinal) ≤ Module.rank ℤ W.toAffine.Point :=
  algebraic_cardinal_rank_lower_bound _ (independent_singleton_of_infinite_order P hP)

end VerifiedLcalc.EllipticCurve
