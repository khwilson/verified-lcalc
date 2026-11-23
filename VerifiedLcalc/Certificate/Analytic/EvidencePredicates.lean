/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Artifacts.Primitives
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic

/-! Predicates for interpreting the submitted analytic evidence records. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Supported mathematical interpretation. Elliptic subjects await an
independent theorem identifying their L-function. -/
def Subject.Denotes (subject : Subject) (f : ℂ → ℂ) : Prop :=
  match subject with
  | .monomial n => f = (fun z : ℂ => z ^ n)
  | .ellipticCurve _ _ => False

/-- Data checks alone cannot supply an elliptic-curve interpretation. -/
theorem ellipticCurve_not_denotes (e : (WeierstrassCurve ℤ))
    (n : Normalization) (f : ℂ → ℂ) :
    ¬ (Subject.ellipticCurve e n).Denotes f := by
  simp [Subject.Denotes]

end VerifiedLcalc.Artifacts

namespace VerifiedLcalc.NumericalRanks

/-- Coordinatewise bounds for the first `n` derivatives; this asserts
smallness only and does not claim exact vanishing. -/
def SmallDerivatives (f : ℂ → ℂ) (center : ℂ) (n : Nat) (eps : Rat) : Prop :=
  ∀ k < n, |(iteratedDeriv k f center).re| ≤ (eps : ℝ) ∧
    |(iteratedDeriv k f center).im| ≤ (eps : ℝ)

/-- Extra hypothesis needed to turn small derivatives into exact zeros. -/
def ExactVanishingHypothesis (f : ℂ → ℂ) (center : ℂ) (n : Nat) (eps : Rat) : Prop :=
  ∀ k < n, (|(iteratedDeriv k f center).re| ≤ (eps : ℝ) ∧
    |(iteratedDeriv k f center).im| ≤ (eps : ℝ)) → iteratedDeriv k f center = 0

/-- Every nonzero derivative in the prefix has a coordinate separated from zero
by the proposed positive gap. This is an explicit hypothesis, not a consequence
of working precision. -/
def NonzeroDerivativeGap (f : ℂ → ℂ) (center : ℂ) (n : Nat) (gap : Rat) : Prop :=
  ∀ k < n, iteratedDeriv k f center ≠ 0 →
    (gap : ℝ) ≤ |(iteratedDeriv k f center).re| ∨
      (gap : ℝ) ≤ |(iteratedDeriv k f center).im|

end VerifiedLcalc.NumericalRanks
