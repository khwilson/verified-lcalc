module

/-! Primitive exact enclosures stored by certificate payloads. -/

@[expose] public section

namespace VerifiedLcalc

/-- Closed rational rectangle in the real and imaginary coordinates. -/
structure Box where
  /-- Lower real endpoint. -/
  reLo : Rat
  /-- Upper real endpoint. -/
  reHi : Rat
  /-- Lower imaginary endpoint. -/
  imLo : Rat
  /-- Upper imaginary endpoint. -/
  imHi : Rat
  deriving Repr, DecidableEq

/-- Bounds are ordered. -/
def Box.valid (b : Box) : Bool :=
  decide (b.reLo ≤ b.reHi ∧ b.imLo ≤ b.imHi)

/-- The rectangle is exactly the singleton zero. -/
def Box.isZero (b : Box) : Bool :=
  decide (b.reLo = 0 ∧ b.reHi = 0 ∧ b.imLo = 0 ∧ b.imHi = 0)

/-- At least one coordinate interval strictly excludes zero. -/
def Box.excludesZero (b : Box) : Bool :=
  decide (0 < b.reLo ∨ b.reHi < 0 ∨ 0 < b.imLo ∨ b.imHi < 0)

/-- Exact predicate that a valid closed rectangle lies within the coordinatewise
cutoff. -/
def Box.WithinCutoff (b : Box) (eps : Rat) : Prop :=
  0 ≤ eps ∧ b.reLo ≤ b.reHi ∧ b.imLo ≤ b.imHi ∧
    -eps ≤ b.reLo ∧ b.reHi ≤ eps ∧ -eps ≤ b.imLo ∧ b.imHi ≤ eps

theorem Box.valid_correct (b : Box) :
    b.valid = true ↔ b.reLo ≤ b.reHi ∧ b.imLo ≤ b.imHi := by
  simp [valid]

theorem Box.isZero_correct (b : Box) :
    b.isZero = true ↔ b.reLo = 0 ∧ b.reHi = 0 ∧ b.imLo = 0 ∧ b.imHi = 0 := by
  simp [isZero]

theorem Box.excludesZero_correct (b : Box) :
    b.excludesZero = true ↔ 0 < b.reLo ∨ b.reHi < 0 ∨ 0 < b.imLo ∨ b.imHi < 0 := by
  simp [excludesZero]

end VerifiedLcalc

namespace VerifiedLcalc.Numerics

/-- Exact rational interval, represented by its lower and upper endpoints. -/
abbrev RealInterval := Rat × Rat

end VerifiedLcalc.Numerics
