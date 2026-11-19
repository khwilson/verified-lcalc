module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace VerifiedLcalc.Numerics
open Set MeasureTheory

/-- Integrating a positive-decay exponential term over the upper Mellin range. -/
theorem integral_exponential_term (a b : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 1, b * Real.exp (-a * t)) = b / a * Real.exp (-a) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  simp only [mul_one, neg_div_neg_eq]
  ring

/-- A polynomial coefficient bound justifies termwise integration on (1,∞).
Both convergence and the exchange of sum and integral are proved. -/
theorem hasSum_integral_exponential_series (a : ℝ) (ha : 0 < a) (b : ℕ → ℝ)
    (hb : ∀ j, |b j| ≤ ((j + 1 : ℕ) : ℝ) ^ 3) :
    HasSum (fun j : ℕ => b j / (a * (j + 1 : ℕ)) * Real.exp (-a * (j + 1 : ℕ)))
      (∫ t : ℝ in Ioi 1, ∑' j : ℕ, b j * Real.exp (-(a * (j + 1 : ℕ)) * t)) := by
  let F := fun j : ℕ => fun t : ℝ => b j * Real.exp (-(a * (j + 1 : ℕ)) * t)
  have hpos (j : ℕ) : 0 < a * (j + 1 : ℕ) := mul_pos ha (by positivity)
  have hi (j : ℕ) : IntegrableOn (F j) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (hpos j)) 1).const_mul (b j)
  have hnorm (j : ℕ) : (∫ t : ℝ in Ioi 1, ‖F j t‖) =
      |b j| / (a * (j + 1 : ℕ)) * Real.exp (-a * (j + 1 : ℕ)) := by
    simp only [F, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [integral_exponential_term _ _ (hpos j)]
    congr 2; ring
  have hq : ‖Real.exp (-a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hs := (summable_pow_mul_geometric_of_norm_lt_one (2 : ℕ) hq).comp_injective
    (show Function.Injective (fun j : ℕ => j + 1) from fun _ _ h => Nat.add_right_cancel h)
  have hs' := hs.mul_left a⁻¹
  have hbound (j : ℕ) : |b j| / (a * (j + 1 : ℕ)) ≤ a⁻¹ * (j + 1 : ℕ) ^ 2 := by
    apply (div_le_iff₀ (hpos j)).mpr
    calc
      |b j| ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := hb j
      _ = a⁻¹ * (j + 1 : ℕ) ^ 2 * (a * (j + 1 : ℕ)) := by
        field_simp
  have hsum : Summable (fun j : ℕ => ∫ t : ℝ in Ioi 1, ‖F j t‖) := by
    apply hs'.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    intro j
    rw [hnorm]
    have hm := mul_le_mul_of_nonneg_right (hbound j) (Real.exp_pos (-a * (j + 1 : ℕ))).le
    convert hm using 1; simp only [Function.comp_apply]
    rw [show -a * (j + 1 : ℕ) = (j + 1 : ℕ) * (-a) by ring, Real.exp_nat_mul]
    ring
  have h := hasSum_integral_of_summable_integral_norm hi hsum
  convert h using 1
  funext j
  simpa only [F, neg_mul] using (integral_exponential_term (a * (j + 1 : ℕ)) (b j) (hpos j)).symm

end VerifiedLcalc.Numerics
