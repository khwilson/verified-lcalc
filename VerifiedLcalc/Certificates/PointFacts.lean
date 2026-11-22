/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral

/-! # Proof-carrying point data

These records refer to actual affine points and integral points of the supplied
Weierstrass equation. They contain no point-search or checker implementation.
-/

@[expose] public section

namespace VerifiedLcalc

/-- Membership of every supplied coordinate pair on the given equation. -/
structure AffineMembership {R : Type*} [CommRing R] (curve : WeierstrassCurve R) where
  /-- The coordinates in the order supplied to the certifier. -/
  coordinates : List (R × R)
  /-- Each member of the list satisfies the equation. -/
  onCurve : ∀ x y, (x, y) ∈ coordinates → curve.toAffine.Equation x y

/-- A checked affine pair determines a point of an elliptic curve. -/
def AffineMembership.point {R : Type*} [CommRing R] [Nontrivial R]
    {curve : WeierstrassCurve R} [curve.IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) : curve.toAffine.Point :=
  .mk (facts.onCurve _ _ (List.getElem_mem i.isLt))

/-- Lift a checked integral pair to the rational point group. -/
def AffineMembership.rationalPoint {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) :
    (curve.baseChange ℚ).toAffine.Point :=
  curve.pointOfIntegralSolution (facts.coordinates[i]).1 (facts.coordinates[i]).2
    (facts.onCurve _ _ (List.getElem_mem i.isLt))

/-- The lifted point belongs to the set of integral points for the indexed equation. -/
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

/-- Indices into the checked integral coordinates and independence of precisely those points. -/
structure IndependentPointFacts {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (source : AffineMembership curve) where
  /-- Indices selecting the family from the integral-coordinate list. -/
  indices : List Nat
  /-- Every selected index refers to a supplied coordinate pair. -/
  indicesValid : ∀ i ∈ indices, i < source.coordinates.length
  /-- Integer linear independence of the corresponding rational points. -/
  independent : LinearIndependent ℤ (fun i : Fin indices.length =>
    source.rationalPoint ⟨indices[i], indicesValid _ (List.getElem_mem i.isLt)⟩)

/-- The actual rational points selected by the verified source indices. -/
def IndependentPointFacts.points {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] {source : AffineMembership curve}
    (facts : IndependentPointFacts source)
    (i : Fin facts.indices.length) : (curve.baseChange ℚ).toAffine.Point :=
  source.rationalPoint ⟨facts.indices[i], facts.indicesValid _ (List.getElem_mem i.isLt)⟩

/-- Positive exact orders aligned with the supplied rational point list. -/
structure TorsionGeneratorOrderFacts {curve : WeierstrassCurve ℚ} [curve.IsElliptic]
    (source : AffineMembership curve) where
  /-- The order list in the same index order as the points. -/
  orders : List ℕ
  /-- There is one order for every checked point. -/
  length_eq : orders.length = source.coordinates.length
  /-- Each order is positive. -/
  positive : ∀ n ∈ orders, 0 < n
  /-- The actual additive order of each supplied coordinate point. -/
  exactOrder : ∀ i : Fin source.coordinates.length,
    addOrderOf (source.point i) = orders.get (Fin.cast length_eq.symm i)

/-- A proved count of the rational points in the submitted generator list.
This records list length only; it makes no basis or generation claim. -/
structure GeneratorCountFacts (coordinates : List (Rat × Rat)) where
  /-- The submitted LMFDB generator count. -/
  count : ℕ
  /-- The coordinate list has exactly the claimed length. -/
  length_eq : coordinates.length = count

/-- Integral seed points and the complete set of integral y-coordinates over each seed's x. -/
structure IntegralYFiberFacts (curve : WeierstrassCurve ℤ) where
  /-- The supplied integral seed points, in input order. -/
  seeds : AffineMembership curve
  /-- The finite set of all integral y-coordinates at the indexed x-coordinate. -/
  fiber : Fin seeds.coordinates.length → Finset ℤ
  /-- The indexed fiber is exactly the set of solutions of the given equation at that x. -/
  complete : ∀ (i : Fin seeds.coordinates.length) (y : ℤ),
    y ∈ fiber i ↔ curve.toAffine.Equation (seeds.coordinates[i]).1 y

end VerifiedLcalc
