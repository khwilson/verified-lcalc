/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.CentralFinite
public import VerifiedLcalc.EllipticCurve.CentralTail
public import VerifiedLcalc.EllipticCurve.Coefficients

/-! Series evidence records used to justify central-value enclosures. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Remaining analytic obligations for an actual central value. The series
must be the convergent split-Mellin exponential series, not the raw Dirichlet
series evaluated outside its convergence domain. -/
structure CentralSeriesEvidence (r : CentralResult) (value : ℝ) where
  /-- Summands of the split Mellin series. -/
  series : Nat → ℝ
  /-- The summands converge to the actual value. -/
  formula : HasSum series value
  /-- The initial series sum is the exact finite Mellin expression. -/
  finiteSum : (∑ j ∈ Finset.range r.termLimit, series j) =
    centralFiniteValue r.coefficients r.rootNumber (2 * Real.pi / Real.sqrt r.conductor)
  /-- A quadratic-times-geometric majorant for every summand. -/
  majorant : ∀ j, |series j| ≤ ((1 + r.rootNumber : Int).natAbs : ℝ) *
    (((j + 1 : Nat) : ℝ) ^ 2 * (r.geometricUpper : ℝ) ^ (j + 1))

end VerifiedLcalc.EllipticCurve
