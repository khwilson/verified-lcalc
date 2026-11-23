/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Enclosures
public import Mathlib.Basic.Complex.Basic

/-! Exact coordinate-rectangle semantics used by analytic witness structures. -/

@[expose] public section

namespace VerifiedLcalc

/-- A complex value lies in a box when both real coordinates lie in their
closed rational intervals. -/
def Box.Contains (b : Box) (z : ℂ) : Prop :=
  z.re ∈ Set.Icc (b.reLo : ℝ) (b.reHi : ℝ) ∧
    z.im ∈ Set.Icc (b.imLo : ℝ) (b.imHi : ℝ)

/-- Every box in the list encloses the matching value of a sequence. -/
def Encloses : List Box → (ℕ → ℂ) → Prop
  | [], _ => True
  | b :: bs, a => b.Contains (a 0) ∧ Encloses bs (fun k => a (k + 1))

end VerifiedLcalc
