module
public import VerifiedLcalc.EllipticCurve.Modularity.Fourier
@[expose] public section
namespace VerifiedLcalc.Modularity
open Set MeasureTheory Filter Asymptotics
open scoped Topology

private theorem scaled_rpow_bound (f : ℝ → ℂ) (c r : ℝ) (hc : 0 < c)
    (hf : f =O[atTop] (fun t : ℝ => t^r)) :
    (fun t => f (c*t)) =O[atTop] (fun t : ℝ => t^r) := by
  have h := hf.comp_tendsto (tendsto_id.const_mul_atTop hc)
  have hb := (isBigO_refl (fun t : ℝ => t^r) atTop).const_mul_left (c^r)
  apply h.trans
  apply hb.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (Real.mul_rpow hc.le ht.le).symm

/-- Differentiating the genuine scaled Mellin transform at the center.
No modularity axiom occurs: a supplied realization is the only curve input. -/
theorem ModularRealization.mellin_first_derivative {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) :
    MellinConvergent (fun t => Real.log t • m.imaginaryFunction t) 1 ∧
    HasDerivAt (mellin m.imaginaryFunction)
      (mellin (fun t => Real.log t • m.imaginaryFunction t) 1) 1 := by
  let _ := m.arithmetic
  let c : ℝ := (Real.sqrt m.level)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel))
  let f : ℝ → ℂ := (ModularForm.weakFEPair (by decide : (0 : ℤ) < 2) m.form).f
  have he (t : ℝ) : m.imaginaryFunction t = f (c*t) := by
    simp [ModularRealization.imaginaryFunction, f, c, ModularForm.weakFEPair,
      div_eq_mul_inv, mul_comm, Complex.ofReal_mul, Complex.ofReal_inv]
  have hefun : m.imaginaryFunction = (fun t => f (c*t)) := funext he
  have ht : m.imaginaryFunction =O[atTop] (fun t : ℝ => t^(-2 : ℝ)) := by
    rw [hefun]
    exact scaled_rpow_bound f c (-2) hc
      ((CuspForm.isStrongFEPair (by decide : (0 : ℤ) < 2) m.form).hf_top (-2))
  have hct : Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun t : ℝ => c*t) := continuous_const.mul continuous_id
      have h := hcont.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
      simpa only [mul_zero] using h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hc ht
  have hz : m.imaginaryFunction =O[𝓝[>] 0] (fun t : ℝ => t^(-0 : ℝ)) := by
    have h := (CuspForm.isStrongFEPair (by decide : (0 : ℤ) < 2) m.form).hf_zero 0
      |>.comp_tendsto hct
    rw [hefun]
    simpa only [f, Function.comp_def, neg_zero, Real.rpow_zero] using h
  have hi : IntegrableOn m.imaginaryFunction (Ioi 0) := by
    simpa [MellinConvergent] using m.central_mellin_convergent
  exact mellin_hasDerivAt_of_isBigO_rpow hi.locallyIntegrableOn ht (by norm_num) hz (by norm_num)

/-- The logarithmic integrand has the opposite Fricke sign. Thus negative
root number makes the derivative integral twice its upper half. -/
theorem ModularRealization.mellin_log_upper {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (hw : m.rootNumber = -1) :
    mellin (fun t => Real.log t • m.imaginaryFunction t) 1 =
      2 * ∫ t : ℝ in Ioi 1, Real.log t • m.imaginaryFunction t := by
  let g : ℝ → ℂ := fun t => Real.log t • m.imaginaryFunction t
  have hfe (t : ℝ) (ht : 0 < t) : g (1/t) = (1 : ℂ)*(t : ℂ)^2*g t := by
    have h : m.imaginaryFunction (1/t) =
        (m.rootNumber : ℂ)*(t : ℂ)^2*m.imaginaryFunction t := by
      simpa only [ModularRealization.imaginaryFunction, Complex.ofReal_div, Complex.ofReal_one]
        using m.frickeImaginaryAxis t ht
    rw [hw] at h
    simp only [Int.cast_neg, Int.cast_one] at h
    dsimp [g]
    simp only [one_div] at h
    simp only [one_div, Real.log_inv, Complex.real_smul, Complex.ofReal_neg]
    rw [h]
    ring
  have hs := Numerics.mellin_one_split g 1 m.mellin_first_derivative.1 hfe
  simpa [g, mellin, one_add_one_eq_two, integral_indicator, Measure.restrict_restrict,
    measurableSet_Ioi, inter_eq_self_of_subset_right (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))] using hs

/-- L(s) in terms of the scaled Mellin transform in a neighborhood of 1. -/
theorem ModularRealization.formL_scaled_mellin {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (s : ℂ) (hs : s ≠ 0) :
    m.formL s = ((Real.sqrt m.level : ℂ)^(-s) * (2*(Complex.Gammaℂ s)⁻¹)) *
      mellin m.imaginaryFunction s := by
  let _ := m.arithmetic
  have hpos : 0 < Real.sqrt (m.level : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)
  have hscale := mellin_comp_mul_right m.imaginaryFunction s hpos
  have hf : (fun t : ℝ => m.imaginaryFunction (t*Real.sqrt m.level)) =
      (fun t : ℝ => m.form (UpperHalfPlane.ofComplex (Complex.I*t))) := by
    funext t
    simp [ModularRealization.imaginaryFunction, Complex.ofReal_mul, Complex.ofReal_div,
      mul_div_cancel_right₀ _ (show (Real.sqrt m.level : ℂ) ≠ 0 by exact_mod_cast hpos.ne')]
  rw [hf] at hscale
  rw [ModularRealization.formL, ModularForm.L_apply_of_ne_zero _ _ hs,
    CuspForm.Λ_eq_mellin, hscale]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- Exact first-derivative formula for a negative-sign realization. It uses
no numerical gamma or log derivative: the undifferentiated Mellin factor is
exactly zero, so the derivative of the normalization cancels. -/
theorem ModularRealization.deriv_one_re_integral {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (hw : m.rootNumber = -1) :
    (deriv m.formL 1).re = (4*Real.pi / Real.sqrt m.level) *
      ∫ t : ℝ in Ioi 1, Real.log t * (m.imaginaryFunction t).re := by
  let K : ℂ → ℂ := fun s => (Real.sqrt m.level : ℂ)^(-s) * (2*(Complex.Gammaℂ s)⁻¹)
  have hsqrt : (Real.sqrt m.level : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel) : 0 < Real.sqrt (m.level : ℝ)).ne'
  have hK : DifferentiableAt ℂ K 1 := by
    dsimp [K]
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hsqrt)).mul
      (Complex.differentiable_Gammaℂ_inv.differentiableAt.const_mul 2)
  have hzero : mellin m.imaginaryFunction 1 = 0 := by
    rw [Numerics.mellin_one_split m.imaginaryFunction m.rootNumber m.central_mellin_convergent]
    · simp [hw]
    · intro t ht
      simpa [ModularRealization.imaginaryFunction, Complex.ofReal_div] using m.frickeImaginaryAxis t ht
  have hh := hK.hasDerivAt.mul m.mellin_first_derivative.2
  have hEq : (fun s => K s*mellin m.imaginaryFunction s) =ᶠ[𝓝 (1 : ℂ)] m.formL := by
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs
    exact (m.formL_scaled_mellin s hs).symm
  have hd := (hh.congr_of_eventuallyEq hEq.symm).deriv
  rw [hzero, mul_zero, zero_add, m.mellin_log_upper hw] at hd
  have hi : IntegrableOn (fun t => Real.log t • m.imaginaryFunction t) (Ioi 1) := by
    have hi : IntegrableOn (fun t => Real.log t • m.imaginaryFunction t) (Ioi 0) := by
      simpa [MellinConvergent] using m.mellin_first_derivative.1
    exact hi.mono_set (Ioi_subset_Ioi (by norm_num))
  have hK1 : K 1 = ((2*Real.pi / Real.sqrt m.level : ℝ) : ℂ) := by
    dsimp [K]
    rw [Complex.cpow_neg, Complex.cpow_one, Complex.Gammaℂ_one]
    push_cast
    field_simp
  have hir : (∫ t : ℝ in Ioi 1, Real.log t • m.imaginaryFunction t).re =
      ∫ t : ℝ in Ioi 1, Real.log t * (m.imaginaryFunction t).re := by
    trans (∫ t : ℝ in Ioi 1, RCLike.re (Real.log t • m.imaginaryFunction t))
    · exact (integral_re hi).symm
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp [Complex.real_smul]
  rw [hd, hK1]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hir]
  norm_num
  ring

end VerifiedLcalc.Modularity
