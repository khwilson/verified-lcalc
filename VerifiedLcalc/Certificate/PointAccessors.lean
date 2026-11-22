/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.PointMembership
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.GroupTheory.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral

/-! # Helpers that turn checked coordinates into curve points -/

@[expose] public section

namespace VerifiedLcalc

/-- A checked affine pair determines a point of an elliptic curve. -/
def AffineMembership.point {R : Type*} [CommRing R] [Nontrivial R]
    {curve : WeierstrassCurve R} [curve.IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) : curve.toAffine.Point :=
  .mk (facts.onCurve _ _ (List.getElem_mem i.isLt))

/-- Lift a checked integral pair to the rational point group. -/
def AffineMembership.rationalPoint {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) : (curve.baseChange ℚ).toAffine.Point :=
  curve.pointOfIntegralSolution (facts.coordinates[i]).1 (facts.coordinates[i]).2
    (facts.onCurve _ _ (List.getElem_mem i.isLt))

/-- The lifted point belongs to the integral points for the indexed equation. -/
theorem AffineMembership.rationalPoint_integral {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) :
    facts.rationalPoint i ∈ curve.integralPoints :=
  WeierstrassCurve.pointOfIntegralSolution_mem _ _ _ _

/-- Empty membership data, used when the integral-coordinate list is absent. -/
def AffineMembership.empty {R : Type*} [CommRing R]
    (curve : WeierstrassCurve R) : AffineMembership curve :=
  ⟨[], fun _ _ h => (List.not_mem_nil h).elim⟩

/-- A source index whose checked integral point has infinite order. -/
abbrev InfiniteOrderPointFact {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (source : AffineMembership curve) :=
  { i : Fin source.coordinates.length // ¬ IsOfFinAddOrder (source.rationalPoint i) }

end VerifiedLcalc
