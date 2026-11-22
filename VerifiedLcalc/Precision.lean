module

public import VerifiedLcalc.Certificates.Enclosures
public import VerifiedLcalc.Certificates.PrecisionPolicy
public import VerifiedLcalc.Scan

/-! # Precision cutoffs for exact rational boxes -/

@[expose] public section

namespace VerifiedLcalc

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
