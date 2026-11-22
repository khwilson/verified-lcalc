/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! # Input claim structures for local rows and isogenies -/

@[expose] public section

namespace VerifiedLcalc

/-- Optional claims from an LMFDB local row. The reduction codes are 0 for
additive, 1 for split multiplicative and -1 for nonsplit multiplicative. -/
structure LocalReductionClaim where
  /-- Rational prime at which the local claims are made. -/
  prime : Nat
  /-- Exponent of this prime in the absolute minimal discriminant. -/
  discriminantValuation : Option Nat := none
  /-- Exponent of this prime in the checked modular conductor. -/
  conductorValuation : Option Nat := none
  /-- Exponent of this prime in the reduced denominator of the rational j-invariant. -/
  jDenominatorValuation : Option Nat := none
  /-- Signed Frobenius trace code for bad reduction. -/
  reductionType : Option Int := none
  /-- Claimed intrinsic local component-group order. -/
  tamagawaNumber : Option Nat := none
  /-- Claimed PARI Kodaira code. Additive codes request a family check. -/
  kodairaSymbol : Option Int := none
/-- A single oriented edge claim with an exact integral target equation. -/
structure IsogenyEdgeClaim where
  /-- Target equation for the rational map. -/
  target : WeierstrassCurve ℤ
  /-- Claimed minimum degree in this direction. -/
  degree : Nat
  /-- Optional x-coordinate of a kernel point with y=0. -/
  kernelX : Option Rat := none

end VerifiedLcalc
