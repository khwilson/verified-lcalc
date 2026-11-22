module

public import Std
public import Init.Data.Rat
public import VerifiedLcalc.Certificates.Enclosures

/-! A conservative rank search on exact rational rectangles. No floating point
or tolerance test is used. A rectangle containing zero is inconclusive unless
it is the singleton zero. -/

@[expose] public section
namespace VerifiedLcalc

/-- Finite evidence for the first nonzero derivative: all earlier boxes are
singleton zero, and the selected box excludes zero. -/
inductive Witness : List Box → Nat → Prop
  | here {b bs} : b.valid = true → b.excludesZero = true → Witness (b :: bs) 0
  | next {b bs n} : b.valid = true → b.isZero = true → Witness bs n →
      Witness (b :: bs) (n + 1)

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

/-- Proof-carrying output of the executable core. -/
structure Certificate (bs : List Box) where
  rank : Nat
  computed : scan bs = some rank
  sound : Witness bs rank

/-- A result is constructed only after checking the exact search equation. -/
def certify (bs : List Box) : Option (Certificate bs) :=
  match h : scan bs with
  | none => none
  | some n => some ⟨n, h, scan_correct bs n h⟩

theorem certify_correct (bs : List Box) (c : Certificate bs)
    (_h : certify bs = some c) : scan bs = some c.rank ∧ Witness bs c.rank :=
  ⟨c.computed, c.sound⟩

end VerifiedLcalc
