module

public import VerifiedLcalc.Scan

@[expose] public section

namespace VerifiedLcalc

/-- Global default for numerical rank observations. Individual requests retain
their own immutable copy, so a policy change cannot reinterpret old evidence. -/
structure PrecisionPolicy where
  precisionBits : Nat
  deriving Repr, DecidableEq

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

/-- The entire rectangle, not just its midpoint, lies inside the coordinatewise
cutoff. Invalid rectangles and negative cutoffs cannot pass. -/
def Box.withinCutoff (b : Box) (eps : Rat) : Bool :=
  decide (0 ≤ eps ∧ b.reLo ≤ b.reHi ∧ b.imLo ≤ b.imHi ∧
    -eps ≤ b.reLo ∧ b.reHi ≤ eps ∧ -eps ≤ b.imLo ∧ b.imHi ≤ eps)

theorem Box.withinCutoff_correct (b : Box) (eps : Rat) :
    b.withinCutoff eps = true ↔
      0 ≤ eps ∧ b.reLo ≤ b.reHi ∧ b.imLo ≤ b.imHi ∧
        -eps ≤ b.reLo ∧ b.reHi ≤ eps ∧ -eps ≤ b.imLo ∧ b.imHi ≤ eps := by
  simp [withinCutoff]

end VerifiedLcalc
