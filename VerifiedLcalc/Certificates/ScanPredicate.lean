/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.Enclosures

/-! Finite mathematical witness predicate for ordered derivative boxes. -/

@[expose] public section

namespace VerifiedLcalc

/-- All boxes before the selected rank are singleton zero, and the selected
box is valid and excludes zero. -/
inductive Witness : List Box → Nat → Prop
  | here {b bs} : b.valid = true → b.excludesZero = true → Witness (b :: bs) 0
  | next {b bs n} : b.valid = true → b.isZero = true → Witness bs n →
      Witness (b :: bs) (n + 1)

end VerifiedLcalc
