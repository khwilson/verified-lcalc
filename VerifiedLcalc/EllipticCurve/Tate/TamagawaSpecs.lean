/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Data.Int.GCD

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

/-- Translate the candidate cusp to the origin at a prime above three, keeping unit scale.
The subsequent terminal divisibility tests decide whether this model supports type III. -/
def tameTypeIIIShift (e : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve.VariableChange ℤ :=
  let r := (-e.b₂ * Nat.gcdA 12 p) % (p : ℤ)
  let t := (-(e.a₃ + r * e.a₁) * Nat.gcdA 2 p) % (p : ℤ)
  ⟨1, r, 0, t⟩

/-- Check the exact terminal type III divisibilities on the translated equation. -/
def checkTameTypeIII (e : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  let model := tameTypeIIIShift e p • e
  decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ^ 2 ∣ model.a₆ ∧ ¬ (p : ℤ) ^ 3 ∣ model.b₈)

/-- The checked Tamagawa factor for good, I₁, I₂ or supported tame III reduction. -/
def tamagawaExpected? (e : WeierstrassCurve ℤ) (p : ℕ) : Option ℕ :=
  if supportsTamagawaOne e p then some 1
  else if multiplicativeIndexTwo e p then some 2
  else if checkTameTypeIII e p then some 2
  else none

end VerifiedLcalc.EllipticCurve
