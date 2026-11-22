/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! # The coordinate membership witness structure -/

@[expose] public section

namespace VerifiedLcalc

/-- Membership of every supplied coordinate pair on the given equation. -/
structure AffineMembership {R : Type*} [CommRing R] (curve : WeierstrassCurve R) where
  /-- The coordinates in the order supplied to the certifier. -/
  coordinates : List (R × R)
  /-- Each member of the list satisfies the equation. -/
  onCurve : ∀ x y, (x, y) ∈ coordinates → curve.toAffine.Equation x y

end VerifiedLcalc
