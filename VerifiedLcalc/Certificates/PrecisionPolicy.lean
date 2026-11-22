module

/-! Immutable precision configuration shared by numerical certificates. -/

@[expose] public section

namespace VerifiedLcalc

/-- Immutable precision settings recorded in numerical evidence. -/
structure PrecisionPolicy where
  /-- Number of binary precision bits requested by the exact evaluator. -/
  precisionBits : Nat
  deriving Repr, DecidableEq

/-- Default immutable policy used by legacy producers. -/
def globalPrecision : PrecisionPolicy := ⟨53⟩

/-- PARI-style half-bit cutoff, version 1: 2^(1-floor(bits/2)).
This is a classification threshold, not a bound on evaluator rounding error. -/
def PrecisionPolicy.cutoff (p : PrecisionPolicy) : Rat :=
  2 / (2 ^ (p.precisionBits / 2) : Nat)

theorem PrecisionPolicy.cutoff_correct (p : PrecisionPolicy) :
    p.cutoff = 2 / (2 ^ (p.precisionBits / 2) : Nat) := rfl

theorem globalPrecision_correct :
    globalPrecision.precisionBits = 53 ∧ globalPrecision.cutoff = 1 / 33554432 := by
  decide +kernel

end VerifiedLcalc
