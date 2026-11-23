/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.RationalPlace
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Localization of `𝓞 ℚ` at a rational prime -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The localization of the rational integers at the canonical prime above `p`. -/
abbrev RationalLocalRing (p : Nat) [Fact p.Prime] :=
  Localization.AtPrime (rationalPlace p).asIdeal

end VerifiedLcalc.EllipticCurve
