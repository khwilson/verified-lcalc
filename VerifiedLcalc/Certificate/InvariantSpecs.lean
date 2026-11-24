/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.Rat.Defs

/-! # Integer quantities in rational elliptic-curve invariants -/

@[expose] public section

namespace VerifiedLcalc.Certification

/-- The absolute product of the reduced abc triple of `j/1728`. -/
def abcProduct (j : ℚ) : ℕ :=
  let t := j / 1728
  let c : ℤ := t.den
  (t.num * (c - t.num) * c).natAbs

/-- The integer whose logarithm is the numerator of the modified Szpiro ratio. -/
def modifiedSzpiroNumerator (curve : WeierstrassCurve ℤ) : ℕ :=
  max (curve.c₄.natAbs ^ 3) (curve.c₆.natAbs ^ 2)

end VerifiedLcalc.Certification
