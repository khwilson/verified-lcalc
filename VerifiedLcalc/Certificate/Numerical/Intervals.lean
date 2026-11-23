/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Basic.Real.Basic

/-! Primitive exact enclosures stored by certificate payloads. -/

@[expose] public section

namespace VerifiedLcalc

deriving instance Repr for Box
deriving instance DecidableEq for Box

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

/-- The validity check compares both pairs of endpoints. -/
theorem Box.valid_correct (b : Box) :
    b.valid = true ↔ b.reLo ≤ b.reHi ∧ b.imLo ≤ b.imHi := by
  simp [valid]

/-- The singleton-zero check succeeds exactly when all four endpoints vanish. -/
theorem Box.isZero_correct (b : Box) :
    b.isZero = true ↔ b.reLo = 0 ∧ b.reHi = 0 ∧ b.imLo = 0 ∧ b.imHi = 0 := by
  simp [isZero]

/-- The exclusion check succeeds exactly when a coordinate interval lies strictly
to one side of zero. -/
theorem Box.excludesZero_correct (b : Box) :
    b.excludesZero = true ↔ 0 < b.reLo ∨ b.reHi < 0 ∨ 0 < b.imLo ∨ b.imHi < 0 := by
  simp [excludesZero]

end VerifiedLcalc

namespace VerifiedLcalc.Numerics

/-- Exact rational interval, represented by its lower and upper endpoints. -/
abbrev RealInterval := Rat × Rat

/-- A real value lies inside a rational interval exactly when it belongs to
the corresponding closed interval after casting its endpoints. -/
def RealInterval.Contains (i : RealInterval) (x : ℝ) : Prop :=
  x ∈ Set.Icc (i.1 : ℝ) (i.2 : ℝ)

end VerifiedLcalc.Numerics
