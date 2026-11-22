/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! # Supplied abscissa support for integral curve points -/

@[expose] public section

namespace VerifiedLcalc

/-- A finite list containing the abscissa of every affine integral solution. -/
structure IntegralXSupport (curve : WeierstrassCurve ℤ) where
  /-- The supplied abscissae. -/
  xs : List ℤ
  /-- Every affine integral solution has its abscissa on the list. -/
  covers : ∀ x y : ℤ, curve.toAffine.Equation x y → x ∈ xs

end VerifiedLcalc
