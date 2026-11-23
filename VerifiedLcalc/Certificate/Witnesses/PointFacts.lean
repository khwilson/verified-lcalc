/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.PointAccessors

/-! # Point family and order witness structures -/

@[expose] public section

namespace VerifiedLcalc

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
