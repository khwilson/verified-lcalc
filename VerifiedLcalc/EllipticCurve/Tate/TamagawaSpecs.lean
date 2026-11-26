/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
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

/-- Check the terminal type III divisibilities for the exact submitted change of variables. -/
def checkTameTypeIII (e : WeierstrassCurve ℤ) (p : ℕ) (shift : TamagawaTypeIIIShift) : Bool :=
  let model := typeIIIChange shift • e
  decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ^ 2 ∣ model.a₆ ∧ ¬ (p : ℤ) ^ 3 ∣ model.b₈)

/-- Check the supported Tamagawa route for the supplied evidence, if any. -/
def tamagawaExpected? (e : WeierstrassCurve ℤ) (p : ℕ)
    (shift : Option TamagawaTypeIIIShift := none) : Option ℕ :=
  match shift with
  | some change => if checkTameTypeIII e p change then some 2 else none
  | none =>
    if supportsTamagawaOne e p then some 1
    else if multiplicativeIndexTwo e p then some 2
    else none

end VerifiedLcalc.EllipticCurve
