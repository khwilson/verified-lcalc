/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.FirstDerivative
public import VerifiedLcalc.Numerics.MellinLogMoments

/-!
# The second derivative of the scaled central Mellin transform

For a supplied weight-two modular realization, write
`M(s) = mellin m.imaginaryFunction s`, with kernel `f(i t / √N)`.
The second derivative inserts `(log t)²`, which preserves the Fricke sign.

The ordinary `m.formL` is the product of this transform with the normalization
in `ModularRealization.formL_scaled_mellin`. Its second derivative reduces to
`(2π/√N) * M''(1)` when both `M(1)` and `M'(1)` vanish exactly.
-/

public section

namespace VerifiedLcalc.Modularity

open MeasureTheory Set

/-- The second derivative of the scaled transform is its second logarithmic moment. -/
theorem ModularRealization.mellin_second_derivative {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) :
    MellinConvergent (fun t => Real.log t ^ 2 • m.imaginaryFunction t) 1 ∧
      iteratedDeriv 2 (mellin m.imaginaryFunction) 1 =
        mellin (fun t => Real.log t ^ 2 • m.imaginaryFunction t) 1 := by
  obtain ⟨ht, hz⟩ := m.imaginaryFunction_decay
  have hi : IntegrableOn m.imaginaryFunction (Ioi 0) := by
    simpa [MellinConvergent] using m.central_mellin_convergent
  exact Numerics.mellin_iteratedDeriv_of_isBigO_rpow 2 hi.locallyIntegrableOn ht (by norm_num)
    hz (by norm_num)

/-- The second moment has the same Fricke sign as the original kernel. -/
theorem ModularRealization.mellin_second_derivative_upper {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) :
    iteratedDeriv 2 (mellin m.imaginaryFunction) 1 =
      (1 + (m.rootNumber : ℂ)) * ∫ t : ℝ in Ioi 1, Real.log t ^ 2 • m.imaginaryFunction t := by
  let g : ℝ → ℂ := fun t => Real.log t ^ 2 • m.imaginaryFunction t
  have hfe (t : ℝ) (ht : 0 < t) : g (1 / t) = (m.rootNumber : ℂ) * (t : ℂ) ^ 2 * g t := by
    have h : m.imaginaryFunction (1 / t) =
        (m.rootNumber : ℂ) * (t : ℂ) ^ 2 * m.imaginaryFunction t := by
      simpa only [ModularRealization.imaginaryFunction, Complex.ofReal_div, Complex.ofReal_one]
        using m.frickeImaginaryAxis t ht
    simp only [one_div] at h
    simp only [g, one_div, Real.log_inv, neg_sq, Complex.real_smul, h]
    ring
  have hs := Numerics.mellin_one_split g m.rootNumber m.mellin_second_derivative.1 hfe
  rw [m.mellin_second_derivative.2]
  simpa [g, mellin, integral_indicator, Measure.restrict_restrict, measurableSet_Ioi,
    inter_eq_self_of_subset_right (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))] using hs

end VerifiedLcalc.Modularity
