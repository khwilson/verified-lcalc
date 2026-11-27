/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Data.ZMod.Basic
public import VerifiedLcalc.Certificate.Witnesses.InputData

/-! # Executable support conditions for intrinsic local Tamagawa factors -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- The exact Tamagawa factor is supported at good reduction and at
multiplicative reduction of index one. -/
def supportsTamagawaOne (e : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  decide (¬ (p : ℤ) ∣ e.Δ) ||
    decide ((p : ℤ) ∣ e.Δ ∧ ¬ (p : ℤ) ^ 2 ∣ e.Δ ∧ ¬ (p : ℤ) ∣ e.c₄)

/-- The integral model has discriminant valuation two and unit c₄ at the given prime. -/
def multiplicativeIndexTwo (e : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  decide ((p : ℤ) ^ 2 ∣ e.Δ ∧ ¬ (p : ℤ) ^ 3 ∣ e.Δ ∧ ¬ (p : ℤ) ∣ e.c₄)

/-- Interpret the submitted coordinates as an integral change with scale one. -/
def typeIIIChange (shift : TamagawaTypeIIIShift) : WeierstrassCurve.VariableChange ℤ :=
  ⟨1, shift.r, shift.s, shift.t⟩

/-- Interpret the submitted type II coordinates as an exact integral change. -/
def typeIIChange (shift : TamagawaTypeIIShift) : WeierstrassCurve.VariableChange ℤ :=
  ⟨1, shift.r, shift.s, shift.t⟩

/-- Interpret the submitted type IV coordinates as a unit-scale translation. -/
def typeIVChange (evidence : TamagawaTypeIVEvidence) : WeierstrassCurve.VariableChange ℤ :=
  ⟨1, evidence.r, evidence.s, evidence.t⟩

/-- The level-one residue quadratic attached to a submitted terminal model. -/
def typeIVResiduePolynomial (model : WeierstrassCurve ℤ) (p : ℕ) (y : ZMod p) : ZMod p :=
  y ^ 2 + ((model.a₃ / (p : ℤ) : ℤ) : ZMod p) * y -
    ((model.a₆ / (p : ℤ) ^ 2 : ℤ) : ZMod p)

/-- Check the terminal type III divisibilities for the exact submitted change of variables. -/
def checkTameTypeIII (e : WeierstrassCurve ℤ) (p : ℕ) (shift : TamagawaTypeIIIShift) : Bool :=
  let model := typeIIIChange shift • e
  decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ^ 2 ∣ model.a₆ ∧ ¬ (p : ℤ) ^ 3 ∣ model.b₈)

/-- Check a submitted scale-one change against the exact tame type II terminal
conditions. This checker performs no search for a change of variables. -/
def checkTameTypeII (e : WeierstrassCurve ℤ) (p : ℕ) (shift : TamagawaTypeIIShift) : Bool :=
  let model := typeIIChange shift • e
  decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ∣ model.a₆ ∧ ¬ (p : ℤ) ^ 2 ∣ model.a₆)

/-- Check the exact submitted type IV change, its terminal conditions, and its
tagged residue evidence. This checker evaluates no finite-field search. -/
def checkTameTypeIV (e : WeierstrassCurve ℤ) (p : ℕ)
    (evidence : TamagawaTypeIVEvidence) : Bool :=
  let model := typeIVChange evidence • e
  let terminal := decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ^ 2 ∣ model.a₆ ∧
    (p : ℤ) ^ 3 ∣ model.b₈ ∧ ¬ (p : ℤ) ^ 3 ∣ model.b₆)
  terminal && match evidence.residue with
  | .root y => decide (y < p ∧ typeIVResiduePolynomial model p (y : ZMod p) = 0)
  | .nonsplitEulerPower value => decide (value + 1 = p ∧
      (((model.a₃ / (p : ℤ)) ^ 2 + 4 * (model.a₆ / (p : ℤ) ^ 2) : ℤ) : ZMod p) ^
        ((p - 1) / 2) = -1)

/-- Check the supported Tamagawa route for the supplied evidence, if any. -/
def tamagawaExpected? (e : WeierstrassCurve ℤ) (p : ℕ)
    (shift : Option TamagawaTypeIIIShift := none)
    (typeIV : Option TamagawaTypeIVEvidence := none)
    (typeII : Option TamagawaTypeIIShift := none) : Option ℕ :=
  match typeII with
  | some change =>
    if shift.isNone && typeIV.isNone && checkTameTypeII e p change then some 1 else none
  | none =>
    match shift, typeIV with
    | some _, some _ => none
    | some change, none => if checkTameTypeIII e p change then some 2 else none
    | none, some evidence => if checkTameTypeIV e p evidence then
        some (match evidence.residue with | .root _ => 3 | .nonsplitEulerPower _ => 1)
      else none
    | none, none =>
      if supportsTamagawaOne e p then some 1
      else if multiplicativeIndexTwo e p then some 2
      else none

end VerifiedLcalc.EllipticCurve
