module

public import VerifiedLcalc.EllipticCurve.Modularity.CentralIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
namespace VerifiedLcalc.Modularity

/-- The actual curve coefficients sum to the realizing cusp form on the
positive imaginary axis. The only input is a modular realization; this general
implication introduces no custom axiom. -/
theorem ModularRealization.imaginaryFunction_hasSum {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => ((WeierstrassCurve.baseChange e ℚ).LFunction n : ℂ) *
      (Real.exp (-(2 * Real.pi / Real.sqrt m.level) * t) : ℂ) ^ n)
      (m.imaginaryFunction t) := by
  letI : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  have hs : 0 < Real.sqrt (m.level : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)
  have him : 0 < (Complex.I * ((t : ℂ) / (Real.sqrt m.level : ℂ))).im := by
    simpa using div_pos ht hs
  have hp : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 m.level : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp only [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have h := ModularForm.hasSum_qExpansion m.form (by norm_num : (0 : ℝ) < 1) hp
    (UpperHalfPlane.ofComplex (Complex.I * ((t : ℂ) / (Real.sqrt m.level : ℂ))))
  have hq : Function.Periodic.qParam 1
      (UpperHalfPlane.ofComplex (Complex.I * ((t : ℂ) / (Real.sqrt m.level : ℂ)))) =
      (Real.exp (-(2 * Real.pi / Real.sqrt m.level) * t) : ℂ) := by
    rw [Function.Periodic.qParam, UpperHalfPlane.ofComplex_apply_of_im_pos him]
    simp only [Complex.ofReal_one, div_one, Complex.ofReal_exp]
    congr 1
    push_cast
    calc
      _ = -(2 * (Real.pi : ℂ) / (Real.sqrt m.level : ℂ)) * (t : ℂ) := by
        linear_combination (2 * (Real.pi : ℂ) * (t : ℂ) / (Real.sqrt m.level : ℂ)) * Complex.I_mul_I
      _ = _ := by ring
  simpa only [m.coefficients, hq, ModularRealization.imaginaryFunction] using h

/-- The real Fourier series with its zero constant coefficient removed. -/
theorem ModularRealization.imaginaryFunction_re_hasSum {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (t : ℝ) (ht : 0 < t) :
    HasSum (fun j : ℕ => ((WeierstrassCurve.baseChange e ℚ).LFunction (j + 1) : ℝ) *
      Real.exp (-(2 * Real.pi / Real.sqrt m.level) * (j + 1 : ℕ) * t))
      (m.imaginaryFunction t).re := by
  have hreal : HasSum (fun n : ℕ =>
      ((WeierstrassCurve.baseChange e ℚ).LFunction n : ℝ) *
        Real.exp (-(2 * Real.pi / Real.sqrt m.level) * t) ^ n)
      (m.imaginaryFunction t).re := by
    convert Complex.hasSum_re (m.imaginaryFunction_hasSum t ht) using 1
    funext n
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
      Complex.intCast_im, Complex.ofReal_im, zero_mul, sub_zero]
  have h' := (hasSum_nat_add_iff' 1).mpr hreal
  have he (j : ℕ) :
      Real.exp (-(2 * Real.pi / Real.sqrt m.level) * (j + 1 : ℕ) * t) =
        Real.exp (-(2 * Real.pi / Real.sqrt m.level) * t) ^ (j + 1) := by
    rw [show -(2 * Real.pi / Real.sqrt m.level) * (j + 1 : ℕ) * t =
      (j + 1 : ℕ) * (-(2 * Real.pi / Real.sqrt m.level) * t) by ring, Real.exp_nat_mul]
  simpa only [he, Finset.sum_range_one, ArithmeticFunction.map_zero, Int.cast_zero,
    pow_zero, zero_mul, sub_zero] using h'

/-- The real upper Mellin integral is the central value with its explicit
normalization. This theorem still has no custom axiom. -/
theorem ModularRealization.central_re_integral {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) :
    (m.formL 1).re = (2 * Real.pi / Real.sqrt m.level) * (1 + (m.rootNumber : ℝ)) *
      (∫ t : ℝ in Set.Ioi 1, (m.imaginaryFunction t).re) := by
  have hi : MeasureTheory.IntegrableOn m.imaginaryFunction (Set.Ioi 1) := by
    have h0 : MeasureTheory.IntegrableOn m.imaginaryFunction (Set.Ioi 0) := by
      simpa [MellinConvergent] using m.central_mellin_convergent
    exact h0.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hm : mellin ((Set.Ioi (1 : ℝ)).indicator m.imaginaryFunction) 1 =
      ∫ t : ℝ in Set.Ioi 1, m.imaginaryFunction t := by
    simp [mellin, MeasureTheory.integral_indicator, MeasureTheory.Measure.restrict_restrict]
  rw [m.central_upper_mellin, hm]
  have hc : (2 * Real.pi / Real.sqrt m.level : ℂ) * (1 + (m.rootNumber : ℂ)) =
      (((2 * Real.pi / Real.sqrt m.level) * (1 + (m.rootNumber : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  exact (integral_re hi).symm

end VerifiedLcalc.Modularity
