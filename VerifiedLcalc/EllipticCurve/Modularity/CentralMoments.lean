/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.FirstDerivative
public import VerifiedLcalc.Numerics.MellinLogMoments
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Central Mellin moments and raw L-function derivatives

For a weight-two realization, the scaled transform uses the kernel
`f(i t / √N)`. Inversion of its log moment multiplies the Fricke sign by
`(-1)^n`. The first surviving raw derivative has the same moment up to the
explicit factor `2π/√N`; every lower completed derivative must vanish exactly.
-/

public section

namespace VerifiedLcalc.Modularity

open MeasureTheory Set Filter
open scoped Topology

/-- Every central derivative of the normalized Mellin transform is a log moment. -/
theorem ModularRealization.mellin_iterated_derivative {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (n : ℕ) :
    MellinConvergent (fun t => Real.log t ^ n • m.imaginaryFunction t) 1 ∧
      iteratedDeriv n (mellin m.imaginaryFunction) 1 =
        mellin (fun t => Real.log t ^ n • m.imaginaryFunction t) 1 := by
  obtain ⟨ht, hz⟩ := m.imaginaryFunction_decay
  have hi : IntegrableOn m.imaginaryFunction (Ioi 0) := by
    simpa [MellinConvergent] using m.central_mellin_convergent
  exact Numerics.mellin_iteratedDeriv_of_isBigO_rpow n hi.locallyIntegrableOn ht (by norm_num)
    hz (by norm_num)

/-- The central nth Mellin derivative is the upper log moment times its parity factor. -/
theorem ModularRealization.mellin_iterated_derivative_upper {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (n : ℕ) :
    iteratedDeriv n (mellin m.imaginaryFunction) 1 =
      (1 + (-1 : ℂ) ^ n * (m.rootNumber : ℂ)) *
        ∫ t : ℝ in Ioi 1, Real.log t ^ n • m.imaginaryFunction t := by
  let g : ℝ → ℂ := fun t => Real.log t ^ n • m.imaginaryFunction t
  have hfe (t : ℝ) (ht : 0 < t) :
      g (1 / t) = ((-1 : ℂ) ^ n * (m.rootNumber : ℂ)) * (t : ℂ) ^ 2 * g t := by
    have h : m.imaginaryFunction (1 / t) =
        (m.rootNumber : ℂ) * (t : ℂ) ^ 2 * m.imaginaryFunction t := by
      simpa only [ModularRealization.imaginaryFunction, Complex.ofReal_div, Complex.ofReal_one]
        using m.frickeImaginaryAxis t ht
    simp only [one_div] at h
    have hlog : Real.log t⁻¹ ^ n = (-1 : ℝ) ^ n * Real.log t ^ n := by
      rw [Real.log_inv, neg_pow]
    simp only [g, one_div]
    rw [hlog, h]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one]
    ring
  have hs := Numerics.mellin_one_split g _ (m.mellin_iterated_derivative n).1 hfe
  rw [(m.mellin_iterated_derivative n).2]
  simpa [g, mellin, integral_indicator, Measure.restrict_restrict, measurableSet_Ioi,
    inter_eq_self_of_subset_right (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))] using hs

/-- In the product rule, exact vanishing of the lower derivatives leaves only the last term. -/
private theorem iteratedDeriv_mul_of_lower_zero {f g : ℂ → ℂ} {n : ℕ} {x : ℂ}
    (hf : ContDiffAt ℂ n f x) (hg : ContDiffAt ℂ n g x)
    (hz : ∀ j < n, iteratedDeriv j g x = 0) :
    iteratedDeriv n (f * g) x = f x * iteratedDeriv n g x := by
  rw [iteratedDeriv_mul hf hg, Finset.sum_eq_single 0]
  · simp
  · intro i hi hne
    have hn : n - i < n := by
      simp only [Finset.mem_range] at hi
      omega
    simp [hz _ hn]
  · simp

/-- The nth raw derivative equals the normalized moment times its central scale when the
lower Mellin derivatives vanish exactly. -/
theorem ModularRealization.formL_iteratedDeriv_of_lower_mellin_zero {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (n : ℕ)
    (hz : ∀ j < n, iteratedDeriv j (mellin m.imaginaryFunction) 1 = 0) :
    iteratedDeriv n m.formL 1 =
      (2 * Real.pi / Real.sqrt m.level : ℂ) * iteratedDeriv n (mellin m.imaginaryFunction) 1 := by
  let K : ℂ → ℂ := fun s => (Real.sqrt m.level : ℂ) ^ (-s) * (2 * (Complex.Gammaℂ s)⁻¹)
  have hpos : 0 < Real.sqrt (m.level : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)
  have hsqrt : (Real.sqrt m.level : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hK : Differentiable ℂ K := by
    dsimp [K]
    exact (differentiable_neg.const_cpow (Or.inl hsqrt)).mul
      (Complex.differentiable_Gammaℂ_inv.const_mul 2)
  have hregion : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 2} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hM : DifferentiableOn ℂ (mellin m.imaginaryFunction) {s : ℂ | 0 < s.re ∧ s.re < 2} := by
    intro s hs
    obtain ⟨ht, hzero⟩ := m.imaginaryFunction_decay
    have hi : IntegrableOn m.imaginaryFunction (Ioi 0) := by
      simpa [MellinConvergent] using m.central_mellin_convergent
    exact (mellin_differentiableAt_of_isBigO_rpow hi.locallyIntegrableOn ht hs.2 hzero
      hs.1).differentiableWithinAt
  have hMC : ContDiffAt ℂ n (mellin m.imaginaryFunction) 1 :=
    (hM.analyticAt (hregion.mem_nhds (by norm_num))).contDiffAt
  have hKC : ContDiffAt ℂ n K 1 := (hK.analyticAt 1).contDiffAt
  have heq : m.formL =ᶠ[𝓝 (1 : ℂ)] K * mellin m.imaginaryFunction := by
    filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs
    exact m.formL_scaled_mellin s hs
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_mul_of_lower_zero hKC hMC hz]
  have hK1 : K 1 = (2 * Real.pi / Real.sqrt m.level : ℂ) := by
    dsimp [K]
    rw [Complex.cpow_neg, Complex.cpow_one, Complex.Gammaℂ_one]
    field_simp
  rw [hK1]

end VerifiedLcalc.Modularity
