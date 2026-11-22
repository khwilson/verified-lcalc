module

public import VerifiedLcalc.Analytic
public import VerifiedLcalc.Upstream.LedvinkaExponential
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-! # Kernel-checked examples of Mathlib interval tactics -/

@[expose] public section
namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Actual kernel-checked use of the pinned interval tactic with rational input. -/
theorem rational_bound : (0 : ℝ) < ((1 / 3 : ℚ) : ℝ) ∧ ((1 / 3 : ℚ) : ℝ) < 1 := by
  dyadic_interval [prec := 8]

/-- Variable polynomial enclosure, including dependency between repeated x. -/
theorem square_bound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : x * x ≤ 1 := by
  dyadic_interval

/-- A concrete positive argument evaluated by the imported exponential extension. -/
theorem exp_one_enclosure :
    Real.exp 1 ∈ Set.Icc (((2718 : ℚ) / 1000 : ℚ) : ℝ) (((2719 : ℚ) / 1000 : ℚ) : ℝ) := by
  dyadic_interval [prec := 20]

/-- Negative exponential weights are needed in central-value evaluation. -/
theorem exp_neg_one_enclosure :
    Real.exp (-1) ∈ Set.Icc (((3678794 : ℚ) / 10000000 : ℚ) : ℝ)
      (((3678795 : ℚ) / 10000000 : ℚ) : ℝ) := by
  dyadic_interval [prec := 28]

/-- Interval arguments use the endpoint-monotonicity proof, not just scalar tests. -/
theorem exp_negative_interval (x : ℝ) (hx : x ∈ Set.Icc (-2 : ℝ) (-1)) :
    Real.exp x ∈ Set.Icc (((13 : ℚ) / 100 : ℚ) : ℝ) (((37 : ℚ) / 100 : ℚ) : ℝ) := by
  dyadic_interval [prec := 20]

end VerifiedLcalc.Numerics
