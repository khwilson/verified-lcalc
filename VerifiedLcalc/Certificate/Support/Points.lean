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
def IndependentPointFacts.points {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] {source : AffineMembership curve}
    (facts : IndependentPointFacts source)
    (i : Fin facts.indices.length) : (curve.baseChange ℚ).toAffine.Point :=
  source.rationalPoint ⟨facts.indices[i], facts.indicesValid _ (List.getElem_mem i.isLt)⟩

end VerifiedLcalc
