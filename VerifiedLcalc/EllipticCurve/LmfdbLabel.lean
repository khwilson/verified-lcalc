/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Data.Nat.Digits.Defs
import Lean.Elab.Tactic.Omega

/-! # The LMFDB base-26 class codes and their numeric interpretation -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Lowercase characters for the canonical base-26 digits, in most-significant order. -/
def lmfdbClassCodeChars (n : ℕ) : List Char :=
  if n = 0 then ['a'] else
    (Nat.digits 26 n).reverse.map fun d => Char.ofNat ('a'.toNat + d)

/-- Encode an LMFDB class number in base 26, from most to least significant digit.
Zero is `a`, 25 is `z`, and 26 is `ba`. -/
def lmfdbClassCode (n : ℕ) : String :=
  String.ofList (lmfdbClassCodeChars n)

/-- Read the numeric value of a lowercase class code by assigning `a = 0` through `z = 25`. -/
def lmfdbClassCodeValue (s : String) : ℕ :=
  Nat.ofDigits 26 (s.toList.reverse.map fun c => c.toNat - 'a'.toNat)

/-- The formatted code recovers the zero-based class number under the producer's decoding. -/
theorem lmfdbClassCodeValue_code (n : ℕ) : lmfdbClassCodeValue (lmfdbClassCode n) = n := by
  by_cases h : n = 0
  · subst n
    decide
  rw [lmfdbClassCode, lmfdbClassCodeChars, ite_eq_right h, lmfdbClassCodeValue,
    String.toList_ofList,
    ← List.map_reverse, List.reverse_reverse, List.map_map]
  have hdigits : (Nat.digits 26 n).map
      ((fun c : Char => c.toNat - 'a'.toNat) ∘ fun d => Char.ofNat ('a'.toNat + d)) =
      (Nat.digits 26 n).map id := by
    refine List.map_congr_left fun d hd => ?_
    have hd' := Nat.digits_lt_base (by decide : 1 < 26) hd
    have hv : Char.isValidCharNat ('a'.toNat + d) := Or.inl (by change 97 + d < 55296; omega)
    rw [Function.comp_apply, Char.ofNat, dite_eq_left hv]
    change (UInt32.ofNatLT _ _).toNat - 'a'.toNat = d
    rw [UInt32.toNat_ofNatLT, Nat.add_sub_cancel_left]
  rw [hdigits, List.map_id, Nat.ofDigits_digits]

/-- Characters of the conductor and class code, in catalogue order. -/
def lmfdbIsoLabelChars (conductor classIndex : ℕ) : List Char :=
  Nat.toDigits 10 conductor ++ '.' :: lmfdbClassCodeChars classIndex

/-- Render the conductor and zero-based isogeny class index in the database's class-label form. -/
def lmfdbIsoLabel (conductor classIndex : ℕ) : String :=
  String.ofList (lmfdbIsoLabelChars conductor classIndex)

/-- Append the one-based reduced minimal curve number to the class label. -/
def lmfdbCurveLabel (conductor classIndex curveNumber : ℕ) : String :=
  String.ofList (lmfdbIsoLabelChars conductor classIndex ++ Nat.toDigits 10 curveNumber)

/-- The class label concatenates the decimal conductor, separator, and base-26 class code. -/
theorem lmfdbIsoLabel_eq (conductor classIndex : ℕ) :
    lmfdbIsoLabel conductor classIndex =
      toString conductor ++ "." ++ lmfdbClassCode classIndex := by
  change String.ofList (Nat.toDigits 10 conductor ++ (['.'] ++ lmfdbClassCodeChars classIndex)) =
    toString conductor ++ "." ++ lmfdbClassCode classIndex
  simp only [String.ofList_append, Nat.toString_eq_ofList_toDigits, String.append_assoc,
    lmfdbClassCode]

/-- The full label appends the decimal curve number to the class label. -/
theorem lmfdbCurveLabel_eq (conductor classIndex curveNumber : ℕ) :
    lmfdbCurveLabel conductor classIndex curveNumber =
      lmfdbIsoLabel conductor classIndex ++ toString curveNumber := by
  rw [lmfdbCurveLabel, String.ofList_append, lmfdbIsoLabel, Nat.toString_eq_ofList_toDigits]

end VerifiedLcalc.EllipticCurve
