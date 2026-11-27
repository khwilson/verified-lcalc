/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

/-! The two representations of submitted residue evidence for type IV. -/

public section

namespace VerifiedLcalc

/-- Supplied residue evidence for the type IV component-group factor. -/
inductive TypeIVTamagawaResidue where
  /-- A specific residue representative at which the terminal quadratic vanishes. -/
  | root (value : Nat)
  /-- The supplied Euler-power value certifying the quadratic is nonsplit at an odd prime. -/
  | nonsplitEulerPower (value : Nat)
  deriving Repr, DecidableEq

end VerifiedLcalc
