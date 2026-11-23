/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Data.Rat.Defs

/-! # Raw special-value claim input -/

@[expose] public section

namespace VerifiedLcalc

/-- An exact rational interpretation of a reported Taylor leading coefficient
and its explicit absolute-error radius. -/
structure SpecialLValueClaim where
  /-- Decimal or rational value as reported by the input. -/
  reported : Rat
  /-- Explicit claimed maximum absolute error. -/
  error : Rat

end VerifiedLcalc
