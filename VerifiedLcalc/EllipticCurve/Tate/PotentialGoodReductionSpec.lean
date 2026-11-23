/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
public import TauCeti.NumberTheory.Padics.RatCast

/-! # Potential good reduction at all rational primes -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Potential good reduction over the rational p-adic integers at every
rational prime. -/
def HasEverywherePotentialGoodReduction (W : WeierstrassCurve ℚ) : Prop :=
  ∀ p : Nat.Primes, (W.baseChange ℚ_[p]).HasPotentialGoodReduction ℤ_[p]

end VerifiedLcalc.EllipticCurve
