/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.PrecisionPolicy

/-! Immutable precision configuration shared by numerical certificates. -/

@[expose] public section

namespace VerifiedLcalc

deriving instance Repr for PrecisionPolicy
deriving instance DecidableEq for PrecisionPolicy

/-- Default immutable policy used by legacy producers. -/
def globalPrecision : PrecisionPolicy := ⟨53⟩

/-- PARI-style half-bit cutoff, version 1: 2^(1-floor(bits/2)).
This is a classification threshold, not a bound on evaluator rounding error. -/
def PrecisionPolicy.cutoff (p : PrecisionPolicy) : Rat :=
  2 / (2 ^ (p.precisionBits / 2) : Nat)

/-- The classification cutoff is determined by half the requested bit count. -/
theorem PrecisionPolicy.cutoff_correct (p : PrecisionPolicy) :
    p.cutoff = 2 / (2 ^ (p.precisionBits / 2) : Nat) := rfl

/-- The default policy uses 53 bits and a cutoff of two to the power of minus 25. -/
theorem globalPrecision_correct :
    globalPrecision.precisionBits = 53 ∧ globalPrecision.cutoff = 1 / 33554432 := by
  decide +kernel

end VerifiedLcalc
