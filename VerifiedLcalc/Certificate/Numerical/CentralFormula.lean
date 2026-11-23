/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-! The exact finite central Mellin expression used by certificate specifications. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Finite initial split-Mellin sum for a coefficient prefix. -/
noncomputable def centralFiniteValue (coefficients : List Int) (rootNumber : Int)
    (alpha : ℝ) : ℝ :=
  (coefficients.zipIdx.map fun (a, j) =>
    ((1 + rootNumber : Int) : ℝ) * (a : ℝ) / (j + 1 : Nat) *
      Real.exp (-alpha * (j + 1 : Nat))).sum

end VerifiedLcalc.EllipticCurve
