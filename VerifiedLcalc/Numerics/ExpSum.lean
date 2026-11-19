module

public import VerifiedLcalc.Numerics.ExpSumCore
public import VerifiedLcalc.Numerics.Exponential
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Mathematical finite sum approximated by the runtime routine. -/
noncomputable def weightedExpSum (terms : List WeightedExpTerm) : ℝ :=
  (terms.map (fun t => (t.coefficient : ℝ) * Real.exp (Dyadic.toReal t.argument))).sum

/-- Sign-aware scalar multiplication preserves the proved exponential enclosure. -/
theorem weightedExpBounds_correct (term : WeightedExpTerm) (prec : Nat) :
    ((weightedExpBounds term prec).1 : ℝ) ≤
      (term.coefficient : ℝ) * Real.exp (Dyadic.toReal term.argument) ∧
    (term.coefficient : ℝ) * Real.exp (Dyadic.toReal term.argument) ≤
      ((weightedExpBounds term prec).2 : ℝ) := by
  have he := expBounds_bounds term.argument prec
  by_cases hc : 0 ≤ term.coefficient
  · have hc' : (0 : ℝ) ≤ (term.coefficient : ℝ) := by exact_mod_cast hc
    simp only [weightedExpBounds, ite_eq_left hc, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left he.1 hc', mul_le_mul_of_nonneg_left he.2 hc'⟩
  · have hc' : (term.coefficient : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    simp only [weightedExpBounds, ite_eq_right hc, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left he.2 hc', mul_le_mul_of_nonpos_left he.1 hc'⟩

/-- Every finite sum computed by the backend encloses the intended real sum. -/
theorem expSumBounds_correct (terms : List WeightedExpTerm) (prec : Nat) :
    ((expSumBounds prec terms).1 : ℝ) ≤ weightedExpSum terms ∧
      weightedExpSum terms ≤ ((expSumBounds prec terms).2 : ℝ) := by
  induction terms with
  | nil => simp [expSumBounds, weightedExpSum]
  | cons term terms ih =>
    have hh := weightedExpBounds_correct term prec
    simpa only [expSumBounds, weightedExpSum, List.map_cons, List.sum_cons, Rat.cast_add]
      using And.intro (add_le_add hh.1 ih.1) (add_le_add hh.2 ih.2)

/-- A proved analytic tail estimate turns the finite enclosure into a bound for
an actual value. This theorem does not assert that the supplied tail is valid. -/
theorem expSumBox_correct (terms : List WeightedExpTerm) (prec : Nat) (tail : ℚ)
    (value : ℝ) (htail : |value - weightedExpSum terms| ≤ (tail : ℝ)) :
    (expSumBox terms prec tail).Contains (Complex.ofReal value) := by
  have hs := expSumBounds_correct terms prec
  have ha := abs_le.mp htail
  constructor
  · change (((expSumBounds prec terms).1 - tail : ℚ) : ℝ) ≤ value ∧
      value ≤ (((expSumBounds prec terms).2 + tail : ℚ) : ℝ)
    push_cast
    constructor <;> linarith [hs.1, hs.2, ha.1, ha.2]
  · change (0 : ℝ) ∈ Set.Icc ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ)
    norm_num

/-- Rank-zero endpoint of the numerical pipeline. The caller must prove
analyticity and the error bound for the real part of the actual central value.
No conclusion can be obtained from an estimated tail or database answer. -/
theorem analyticOrder_zero_of_expSum {f : ℂ → ℂ} {center : ℂ}
    (hf : AnalyticAt ℂ f center) (terms : List WeightedExpTerm) (prec : Nat) (tail : ℚ)
    (htail : |(f center).re - weightedExpSum terms| ≤ (tail : ℝ))
    (hseparated : (expSumBox terms prec tail).excludesZero = true) :
    analyticOrderAt f center = 0 := by
  have hn := Box.excludesZero_sound hseparated
    (expSumBox_correct terms prec tail (f center).re htail)
  apply hf.analyticOrderAt_eq_zero.mpr
  intro hz
  apply hn
  simp [hz]

end VerifiedLcalc.Numerics
