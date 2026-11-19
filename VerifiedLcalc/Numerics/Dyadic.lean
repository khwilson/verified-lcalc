module

public import VerifiedLcalc.Analytic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Finite dyadic interval endpoints exported as the certificate's exact
rational rectangle. Arithmetic is provided by mathlib, not reimplemented here. -/
def boxOfDyadics (rl rh il ih : Dyadic) : Box :=
  ⟨rl.toRat, rh.toRat, il.toRat, ih.toRat⟩

/-- The adapter preserves the real interpretation of Ledvinka's interval type. -/
theorem boxOfDyadics_correct (rl rh il ih : Dyadic) (z : ℂ) :
    (boxOfDyadics rl rh il ih).Contains z ↔
      z.re ∈ Inclusion.Interval.Icc (rl : WithBot Dyadic) (rh : WithTop Dyadic) ∧
      z.im ∈ Inclusion.Interval.Icc (il : WithBot Dyadic) (ih : WithTop Dyadic) := by
  simp [boxOfDyadics, Box.Contains, Set.mem_Icc, mem_iff_mem_map,
    Inclusion.Interval.Icc, Inclusion.Interval.map, Inclusion.Interval.mem_def,
    Dyadic.toReal]

/-- Actual kernel-checked use of the pinned interval tactic with rational input. -/
theorem rational_bound : (0 : ℝ) < ((1 / 3 : ℚ) : ℝ) ∧ ((1 / 3 : ℚ) : ℝ) < 1 := by
  dyadic_interval [prec := 8]

/-- Variable polynomial enclosure, including dependency between repeated x. -/
theorem square_bound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : x * x ≤ 1 := by
  dyadic_interval

end VerifiedLcalc.Numerics
