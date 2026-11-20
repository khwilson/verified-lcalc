/-
SPDX-License-Identifier: GPL-2.0-or-later
The Halberstadt case organization is adapted from PARI/GP elliptic.c,
Copyright (C) 2000 The PARI group, under GPL version 2 or later.
Lean translation and proof interfaces: verified-lcalc contributors, 2026.
See LICENSES/PARI-GPL-2.0-or-later.txt and docs/WILD_ARITHMETIC.md.
-/
module
public import VerifiedLcalc.EllipticCurve.Tate.WildTateCore
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open Artifacts

/-- The three primitive quadratic characters used by the 2-adic table. -/
def twoCharacter (a n : Int) : Int :=
  if a = -1 then ZMod.χ₄ n
  else if a = 2 then ZMod.χ₈ n
  else if a = -2 then ZMod.χ₈' n else 0

/-- Finite encoding of infinite valuation, only for zero c4 or c6. -/
def wildValuation (p : Nat) (a : Int) : Nat :=
  if a = 0 then 12 else padicValNat p a.natAbs

def wildUnit (p modulus : Nat) (a : Int) : Int :=
  (a / (p : Int)^(wildValuation p a)) % (modulus : Int)

/-- The row number in Halberstadt's 2-adic classification. -/
def twoRow (v4 v6 vd : Nat) (kod : Int) : Nat :=
  if kod > 4 then 1 else
  match kod with
  | 1 => if v6 > 0 then 2 else 1
  | 2 => if vd = 4 then 1 else if vd = 7 then 3 else if v4 = 4 then 2 else 4
  | 3 => if vd = 6 then 3 else if vd = 8 then 4 else if vd = 9 then 5 else if v4 = 5 then 2 else 1
  | 4 => if v4 > 4 then 2 else 1
  | -1 => if vd = 9 then 2 else if vd = 10 then 4 else if v4 > 4 then 3 else 1
  | -2 => if vd = 12 then 2 else if vd = 14 then 3 else 1
  | -3 => if vd = 12 then 2 else if vd = 14 then 3 else if vd = 15 then 4 else 1
  | -4 => if v6 = 7 then 2 else 1
  | -5 => if v6 = 7 ∨ v4 = 6 then 2 else 1
  | -6 => if vd = 12 then 2 else if vd = 13 then 3 else if v4 = 6 then 2 else 1
  | -7 => if vd = 12 ∨ v4 = 6 then 2 else 1
  | _ => if v4 = 6 then 2 else 1

/-- Mathematical case table, parameterized by its quadratic characters so the
runtime and mathlib interpretations share the published classification. -/
def twoRootTable (K : Int → Int → Int) (v4 v6 vd : Nat)
    (u v d : Int) (kod : Int) : Int :=
  let row := twoRow v4 v6 vd kod
  let x := u+2*v
  if kod < -9 then if row = 2 then -(K (-1) v) else -1 else
  match kod with
  | 1 => 1
  | 2 => match row with
    | 1 => if v4 = 4 then K (-1) u else if v4 = 5 then 1 else -1
    | 2 => if v6 = 7 then 1 else -1
    | 3 => if v % 8 = 5 ∨ (u*v) % 8 = 5 then 1 else -1
    | _ => if v4 > 5 then K (-1) v else if v4 = 5 then -(K (-1) u) else -1
  | 3 => match row with
    | 1 => -(K 2 (u*v))
    | 2 => -(K 2 v)
    | 3 => let y := (u-v*2^(v6-5)) % 16
           if y = 7 ∨ y = 11 then 1 else -1
    | 4 => if v % 8 = 3 ∨ (2*u+v) % 8 = 7 then 1 else -1
    | _ => if v6 = 8 then K 2 x else K (-2) u
  | -1 => match row with
    | 1 => -(K 2 x)
    | 2 => if v % 8 = 7 ∨ x % 32 = 11 then 1 else -1
    | 3 => if v4 = 6 then 1 else -1
    | _ => if v4 > 6 then K (-1) v else if v4 = 6 then -(K (-1) (u*v)) else -1
  | -2 => if row = 1 then K (-2) v else K (-1) v
  | -3 => match row with
    | 1 => let y := (u-2*v) % 64
           if y = 3 ∨ y = 19 then 1 else -1
    | 2 => K (2*K (-1) u) v
    | 3 => -(K (-1) u) * K (-2*K (-1) u) (u*v)
    | _ => if v6 = 11 then K (-2) x else -(K (-2) u)
  | -5 => if row = 1 then if x % 32 = 23 then 1 else -1 else -(K 2 (2*u+v))
  | -6 => match row with
    | 1 => 1
    | 2 => if v6 = 10 then 1 else -1
    | _ => if u % 16 = 11 ∨ (u+4*v) % 16 = 3 then 1 else -1
  | -7 => if row = 1 then 1 else
    let y := (u+v*2^(v6-8)) % 16
    if v6 = 10 then (if y = 9 ∨ y = 13 then 1 else -1)
    else if y = 9 ∨ y = 5 then 1 else -1
  | -8 => if row = 2 then K (-1) (v*d) else -1
  | -9 => if row = 2 then -(K (-1) d) else -1
  | _ => -1

def threeRow (v4 v6 vd : Nat) (kod : Int) : Nat :=
  if kod.natAbs > 4 then 1 else
  match kod with
  | -1 | 1 => if v4 % 2 = 1 then 2 else 1
  | -3 | 3 => if 2*v6 > vd+3 then 2 else 1
  | -4 | 2 => if vd % 6 = 4 then 3 else if vd % 6 = 5 then 4 else if v6 % 3 = 1 then 2 else 1
  | _ => if vd % 6 = 0 then 2 else if vd % 6 = 1 then 3 else 1

def threeRootTable (K : Int → Int) (v4 v6 vd : Nat)
    (u v d : Int) (kod : Int) : Int :=
  let row := threeRow v4 v6 vd kod
  let r := v % 9
  match kod with
  | 1 | 3 | -3 => 1
  | 2 => match row with
    | 1 => if r = 4 ∨ r > 6 then 1 else -1
    | 2 => -(K u)*K v
    | 3 => 1
    | _ => -(K v)
  | 4 => match row with
    | 1 => K v * K d
    | 2 => -(K u)
    | _ => -(K v)
  | -2 => if row = 2 then 1 else K v
  | -4 => match row with
    | 1 => if v4 = 4 then (if r = 4 ∨ r = 8 then 1 else -1)
           else if r = 1 ∨ r = 2 then 1 else -1
    | 2 => -(K v)
    | 3 => if r = 2 ∨ r = 7 then 1 else -1
    | _ => K v
  | _ => -1

/-- Local sign for a separately checked minimal additive Tate transcript. -/
def wildRoot (e : (WeierstrassCurve ℤ)) (p : Nat) (w : TateWitness) : Int :=
  let v4 := wildValuation p (e.c₄)
  let v6 := wildValuation p (e.c₆)
  let vd := wildValuation p (e.Δ)
  let modulus := if p = 2 then 64 else 81
  let u := wildUnit p modulus (e.c₄)
  let v := wildUnit p modulus (e.c₆)
  let d := wildUnit p modulus (e.Δ)
  if p = 2 then twoRootTable twoCharacter v4 v6 vd u v d w.kodaira
  else threeRootTable (legendreSym 3) v4 v6 vd u v d w.kodaira

structure WildData where
  atTwo : Option TateWitness
  atThree : Option TateWitness
  deriving Repr, DecidableEq

def validWildAt (e : (WeierstrassCurve ℤ)) (p : Nat) (w : Option TateWitness) : Prop :=
  if modelReduction e p = .additive then
    ∃ v, w = some v ∧ v.Valid e p ∧ (wildRoot e p v = 1 ∨ wildRoot e p v = -1)
  else w = none

instance (e : (WeierstrassCurve ℤ)) (p : Nat) (w : Option TateWitness) : Decidable (validWildAt e p w) :=
  if h : modelReduction e p = .additive then
    match w with
    | none => isFalse (by simp [validWildAt, h])
    | some v => decidable_of_iff (v.Valid e p ∧ (wildRoot e p v = 1 ∨ wildRoot e p v = -1))
        (by simp [validWildAt, h])
  else decidable_of_iff (w = none) (by simp [validWildAt, h])

def WildData.Valid (d : WildData) (e : (WeierstrassCurve ℤ)) : Prop :=
  validWildAt e 2 d.atTwo ∧ validWildAt e 3 d.atThree
  deriving Decidable

def wildData? (e : (WeierstrassCurve ℤ)) : Option WildData :=
  let d : WildData := ⟨tateWitness? e 2, tateWitness? e 3⟩
  if d.Valid e then some d else none

theorem wildData?_sound (e : (WeierstrassCurve ℤ)) (d : WildData)
    (h : wildData? e = some d) : d.Valid e := by
  unfold wildData? at h
  dsimp only at h
  split at h
  · next hv => cases h; exact hv
  · simp at h

def wildExponent (e : (WeierstrassCurve ℤ)) (d : WildData) (p : Nat) : Nat :=
  match (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | some w => padicValNat p (e.Δ).natAbs - w.offset
  | none => localExponent e p

def wildLocalRoot (e : (WeierstrassCurve ℤ)) (d : WildData) (p : Nat) : Int :=
  match (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | some w => wildRoot e p w
  | none => localRoot e p

def wildConductorRootFromPrimes (e : (WeierstrassCurve ℤ)) (d : WildData) (ps : List Nat) : Nat × Int :=
  ((ps.map fun p => p^wildExponent e d p).prod, -(ps.map (wildLocalRoot e d)).prod)

end VerifiedLcalc.EllipticCurve
