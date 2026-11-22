/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated

/-! # Algebraic rank interval data -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Checked lower and upper bounds on the Mordell–Weil rank of a nonsingular
rational Weierstrass curve. TauCeti supplies finite generation from the
Mordell–Weil theorem, so the natural-valued `finrank` is the actual rank. -/
structure AlgebraicRankBounds (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic] where
  /-- The claimed lower endpoint. -/
  lower : ℕ
  /-- The claimed upper endpoint. -/
  upper : ℕ
  /-- The actual rank is at least the lower endpoint. -/
  lower_le_finrank : lower ≤ Module.finrank ℤ W.toAffine.Point
  /-- The actual rank is at most the upper endpoint. -/
  finrank_le_upper : Module.finrank ℤ W.toAffine.Point ≤ upper

end VerifiedLcalc.EllipticCurve
