module

public import VerifiedLcalc.Numerics.RationalExpCore
public import VerifiedLcalc.Numerics.Exponential
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

theorem rationalExpBounds_correct (lo hi : Rat) (prec : Nat) (x : ℝ)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    ((rationalExpBounds lo hi prec).1 : ℝ) ≤ Real.exp x ∧
      Real.exp x ≤ ((rationalExpBounds lo hi prec).2 : ℝ) := by
  have hl : (((lo.toDyadic prec).toRat : Rat) : ℝ) ≤ (lo : ℝ) := by
    exact_mod_cast Rat.toRat_toDyadic_le (x := lo) (prec := prec)
  have hu : ((((-hi).toDyadic prec).toRat : Rat) : ℝ) ≤ -(hi : ℝ) := by
    exact_mod_cast Rat.toRat_toDyadic_le (x := -hi) (prec := prec)
  have hupper : (hi : ℝ) ≤ Dyadic.toReal (-((-hi).toDyadic prec)) := by
    simp only [Dyadic.toReal, _root_.Dyadic.toRat_neg, Rat.cast_neg]
    linarith
  exact ⟨(expBounds_bounds (lo.toDyadic prec) prec).1.trans
      (Real.exp_le_exp.mpr (hl.trans hlo)),
    (Real.exp_le_exp.mpr (hhi.trans hupper)).trans
      (expBounds_bounds (-((-hi).toDyadic prec)) prec).2⟩

theorem rationalWeightedBounds_correct (term : RationalExpTerm) (prec : Nat) (x : ℝ)
    (hx : (term.argumentLo : ℝ) ≤ x ∧ x ≤ (term.argumentHi : ℝ)) :
    ((rationalWeightedBounds term prec).1 : ℝ) ≤ (term.coefficient : ℝ) * Real.exp x ∧
      (term.coefficient : ℝ) * Real.exp x ≤ ((rationalWeightedBounds term prec).2 : ℝ) := by
  have he := rationalExpBounds_correct _ _ prec x hx.1 hx.2
  by_cases hc : 0 ≤ term.coefficient
  · have hc' : (0 : ℝ) ≤ (term.coefficient : ℝ) := by exact_mod_cast hc
    simp only [rationalWeightedBounds, ite_eq_left hc, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left he.1 hc', mul_le_mul_of_nonneg_left he.2 hc'⟩
  · have hc' : (term.coefficient : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hc
    simp only [rationalWeightedBounds, ite_eq_right hc, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left he.2 hc', mul_le_mul_of_nonpos_left he.1 hc'⟩

/-- Per-term argument evidence is independent of the evaluator's interval
arithmetic; each true argument can be irrational. -/
theorem rationalExpSumBounds_correct (terms : List RationalExpTerm) (prec : Nat)
    (argument : RationalExpTerm → ℝ)
    (ha : ∀ t ∈ terms, (t.argumentLo : ℝ) ≤ argument t ∧ argument t ≤ (t.argumentHi : ℝ)) :
    ((rationalExpSumBounds prec terms).1 : ℝ) ≤
      (terms.map (fun t => (t.coefficient : ℝ) * Real.exp (argument t))).sum ∧
    (terms.map (fun t => (t.coefficient : ℝ) * Real.exp (argument t))).sum ≤
      ((rationalExpSumBounds prec terms).2 : ℝ) := by
  induction terms with
  | nil => simp [rationalExpSumBounds]
  | cons t ts ih =>
    have hh := rationalWeightedBounds_correct t prec (argument t) (ha t (by simp))
    have ht := ih (fun t hm => ha t (by simp [hm]))
    simpa only [rationalExpSumBounds, List.map_cons, List.sum_cons, Rat.cast_add] using
      And.intro (add_le_add hh.1 ht.1) (add_le_add hh.2 ht.2)

end VerifiedLcalc.Numerics
