/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: verified-lcalc contributors
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
public import VerifiedLcalc.Certificate.PointAccessors

/-! # Compatibility imports and point accessors for legacy callers -/

@[expose] public section

namespace VerifiedLcalc

/-- The actual rational points selected by the verified source indices. -/
def IndependentPointFacts.points {curve : WeierstrassCurve ℚ} [curve.IsElliptic]
    {n : Nat} {source : Fin n → curve.toAffine.Point} (facts : IndependentPointFacts source)
    (i : Fin facts.rank) : curve.toAffine.Point :=
  source (facts.indices i)

/-- The exact orders in source order, available to list-based consumers. -/
def TorsionGeneratorOrderFacts.orders {curve : WeierstrassCurve ℚ} [curve.IsElliptic]
    {source : AffineMembership curve} (facts : TorsionGeneratorOrderFacts source) : List ℕ :=
  List.ofFn facts.order

/-- The number of submitted generator coordinates, derived from their checked membership. -/
def AlgebraicFacts.generatorCount {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (facts : AlgebraicFacts curve) : Option Nat :=
  facts.generators.map fun membership => membership.coordinates.length

end VerifiedLcalc
