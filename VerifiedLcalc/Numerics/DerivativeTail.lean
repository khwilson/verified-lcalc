module
public import VerifiedLcalc.Numerics.FourierInterval
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
@[expose] public section
namespace VerifiedLcalc.Numerics
open MeasureTheory Set

/-- Cubic coefficient bounds give an exponentially decaying Fourier bound
throughout the upper tail, rather than a constant bound on an infinite set. -/
theorem fourier_tail_pointwise (a : Nat → Int) (q Q value : ℝ)
    (hq : 0 ≤ q) (hQ : q ≤ Q) (hr : 8*Q < 1)
    (hf : HasSum (fun j => (a (j+1) : ℝ)*q^(j+1)) value)
    (hb : ∀ j, |(a (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3) :
    |value| ≤ q/(1-8*Q) := by
  have hQr : 0 ≤ Q := hq.trans hQ
  have hg := (hasSum_geometric_of_lt_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hQr) hr).mul_left q
  have h := hf.norm_le_of_bounded hg (by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hq _)]
    calc
      _ ≤ ((j+1 : Nat) : ℝ)^3*q^(j+1) := mul_le_mul_of_nonneg_right (hb j) (pow_nonneg hq _)
      _ ≤ q*(8*q)^j := by simpa [show (2 : ℝ)^3 = 8 by norm_num, mul_comm] using polynomial_geometric_majorant q 3 0 j hq
      _ ≤ q*(8*Q)^j := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) j) hq)
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using h

private theorem t_exp_decay (alpha T t : ℝ) (ha : 0 < alpha) (hT : 0 < T)
    (hstart : 2 ≤ alpha*T) (ht : T ≤ t) :
    t*Real.exp (-alpha*t) ≤ T*Real.exp (-alpha*T/2)*Real.exp (-alpha*t/2) := by
  have hdiff : 0 ≤ t-T := sub_nonneg.mpr ht
  have harg : (t-T)/T ≤ alpha*(t-T)/2 := by
    apply (div_le_iff₀ hT).mpr
    have hmul := mul_nonneg (sub_nonneg.mpr hstart) hdiff
    nlinarith
  have h : t ≤ T*Real.exp (alpha*(t-T)/2) := by
    have he := (Real.add_one_le_exp ((t-T)/T)).trans (Real.exp_le_exp.mpr harg)
    have he' := mul_le_mul_of_nonneg_left he hT.le
    convert he' using 1 <;> field_simp <;> ring
  have he := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-alpha*t))
  calc
    _ ≤ T*Real.exp (alpha*(t-T)/2)*Real.exp (-alpha*t) := he
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 1
      ring

/-- Absolute upper-tail error for the logarithmic Mellin integrand. -/
theorem derivative_tail_error (a : Nat → Int) (f : ℝ → ℝ) (alpha al T Q : ℝ)
    (hal : 0 < al) (ha : al ≤ alpha) (hT : 1 ≤ T) (hstart : 2 ≤ al*T)
    (hQ : Real.exp (-alpha*T) ≤ Q) (hr : 8*Q < 1)
    (hf : ∀ t, 0 < t → HasSum (fun j => (a (j+1) : ℝ)*Real.exp (-alpha*t)^(j+1)) (f t))
    (hb : ∀ j, |(a (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3)
    (hi : IntegrableOn (fun t => Real.log t*f t) (Ioi T)) :
    |∫ t : ℝ in Ioi T, Real.log t*f t| ≤ 2*T/al*Q/(1-8*Q) := by
  have hap : 0 < alpha := hal.trans_le ha
  have hTp : 0 < T := by linarith
  have hQ0 : 0 ≤ Q := (Real.exp_pos _).le.trans hQ
  have hden : 0 < 1-8*Q := by linarith
  let C := T*Real.exp (-alpha*T/2)/(1-8*Q)
  have hmajor : IntegrableOn (fun t : ℝ => C*Real.exp ((-alpha/2)*t)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith : -alpha/2 < 0) T).const_mul C
  have hbound (t : ℝ) (ht : t ∈ Ioi T) :
      ‖Real.log t*f t‖ ≤ C*Real.exp ((-alpha/2)*t) := by
    have htp : 0 < t := hTp.trans ht
    have hqt : Real.exp (-alpha*t) ≤ Q := by
      apply le_trans (b := Real.exp (-alpha*T)) _ hQ
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hap.le (sub_nonneg.mpr ht.le)]
    have hfb := fourier_tail_pointwise a (Real.exp (-alpha*t)) Q (f t)
      (Real.exp_nonneg _) hqt hr (hf t htp) hb
    have hlog : 0 ≤ Real.log t := Real.log_nonneg (hT.trans ht.le)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog]
    calc
      _ ≤ t*(Real.exp (-alpha*t)/(1-8*Q)) :=
        mul_le_mul (Real.log_le_self htp.le) hfb (abs_nonneg _) (by positivity)
      _ ≤ T*Real.exp (-alpha*T/2)*Real.exp (-alpha*t/2)/(1-8*Q) := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hden.le
        exact t_exp_decay alpha T t hap hTp (by nlinarith) ht.le
      _ = _ := by dsimp [C]; congr 1 <;> ring
  have hnorm := norm_integral_le_integral_norm (f := fun t : ℝ => Real.log t*f t)
    (μ := volume.restrict (Ioi T))
  have hm := integral_mono_ae hi.norm hmajor
    (ae_restrict_mem measurableSet_Ioi |>.mono hbound)
  have hcalc : (∫ t : ℝ in Ioi T, C*Real.exp ((-alpha/2)*t)) =
      2*T/alpha*Real.exp (-alpha*T)/(1-8*Q) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -alpha/2 < 0)]
    dsimp [C]
    rw [show (-alpha/2)*T = -alpha*T/2 by ring]
    have he : Real.exp (-alpha*T/2)*Real.exp (-alpha*T/2) = Real.exp (-alpha*T) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← he]
    field_simp [hap.ne', hden.ne']
    <;> ring
  have hfin := hnorm.trans hm
  rw [Real.norm_eq_abs, hcalc] at hfin
  apply hfin.trans
  apply div_le_div_of_nonneg_right _ hden.le
  exact mul_le_mul (by gcongr) hQ (Real.exp_nonneg _) (by positivity)

end VerifiedLcalc.Numerics
