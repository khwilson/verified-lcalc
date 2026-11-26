/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

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

/-- The checked Tamagawa factor for good reduction or multiplicative index one or two. -/
def tamagawaExpected? (e : WeierstrassCurve ℤ) (p : ℕ) : Option ℕ :=
  if supportsTamagawaOne e p then some 1
  else if multiplicativeIndexTwo e p then some 2
  else none

end VerifiedLcalc.EllipticCurve
