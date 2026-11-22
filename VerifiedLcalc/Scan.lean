/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Std
public import Init.Data.Rat
public import VerifiedLcalc.Certificates.Scan

/-! A conservative rank search on exact rational rectangles. No floating point
or tolerance test is used. A rectangle containing zero is inconclusive unless
it is the singleton zero. -/

@[expose] public section
namespace VerifiedLcalc

/-- Search only as far as the supplied boxes. `none` means insufficient evidence
(including exhaustion or malformed bounds), never a claim of infinite rank. -/
def scan : List Box → Option Nat
  | [] => none
  | b :: bs =>
    if b.valid then
      if b.excludesZero then some 0
      else if b.isZero then (scan bs).map Nat.succ
      else none
    else none

/-- Each successful search has a logical certificate. -/
theorem scan_correct (bs : List Box) (n : Nat) :
    scan bs = some n → Witness bs n := by
  induction bs generalizing n with
  | nil => simp [scan]
  | cons b bs ih =>
    simp only [scan]
    split <;> rename_i hv
    · split <;> rename_i hn
      · intro h
        cases h
        exact Witness.here hv hn
      · split <;> rename_i hz
        · cases hs : scan bs with
          | none => simp
          | some k =>
            simp only [Option.map_some, Option.some.injEq]
            intro h
            subst n
            exact Witness.next hv hz (ih k hs)
        · simp
    · simp

/-- Every mathematical witness is accepted by the executable scan. -/
theorem witness_scan {bs : List Box} {n : Nat} (h : Witness bs n) :
    scan bs = some n := by
  induction h with
  | here hv hn => simp [scan, hv, hn]
  | @next b bs n hv hz h ih =>
    obtain ⟨hrl, hrh, hil, hih⟩ := b.isZero_correct.mp hz
    simp [scan, hv, hz, ih, Box.excludesZero, hrl, hrh, hil, hih]

/-- The raw certificate stores a mathematical witness. This compatibility
theorem exposes the historical executable projection. -/
theorem Certificate.computed {bs : List Box} (c : Certificate bs) :
    scan bs = some c.rank := witness_scan c.sound

/-- A result is constructed only after checking the exact search equation. -/
def certify (bs : List Box) : Option (Certificate bs) :=
  match h : scan bs with
  | none => none
  | some n => some ⟨n, scan_correct bs n h⟩

theorem certify_correct (bs : List Box) (c : Certificate bs)
    (_h : certify bs = some c) : scan bs = some c.rank ∧ Witness bs c.rank :=
  ⟨Certificate.computed c, c.sound⟩

end VerifiedLcalc
