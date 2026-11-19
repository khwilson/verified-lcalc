module

public import VerifiedLcalc.Scan

@[expose] public section

namespace VerifiedLcalc.Examples

/-- Three exactly vanishing derivatives followed by a nonzero third derivative.
This is a polynomial test case, not an elliptic-curve L-function. -/
def cubicBoxes : List Box :=
  [⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨6, 6, 0, 0⟩]

theorem cubicBoxes_computes : scan cubicBoxes = some 3 := by decide

example : scan [] = none := rfl
example : scan [⟨-1, 1, -1, 1⟩] = none := by decide
example : scan [⟨0, 0, 0, 0⟩] = none := by decide
example : scan [⟨2, 1, 0, 0⟩] = none := by decide
example : scan [⟨0, 0, 1, 2⟩] = some 0 := by decide
-- A nonzero later derivative cannot certify vanishing of an earlier one.
example : scan [⟨-1, 1, 0, 0⟩, ⟨1, 2, 0, 0⟩] = none := by decide

end VerifiedLcalc.Examples
