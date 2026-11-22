/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.CentralMoments

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
        mellin (fun t => Real.log t ^ 2 • m.imaginaryFunction t) 1 :=
  m.mellin_iterated_derivative 2

/-- The second moment has the same Fricke sign as the original kernel. -/
theorem ModularRealization.mellin_second_derivative_upper {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) :
    iteratedDeriv 2 (mellin m.imaginaryFunction) 1 =
      (1 + (m.rootNumber : ℂ)) * ∫ t : ℝ in Ioi 1, Real.log t ^ 2 • m.imaginaryFunction t := by
  simpa using m.mellin_iterated_derivative_upper 2

/-- The second raw L-derivative is the scaled upper second moment when both lower
Mellin derivatives vanish. -/
theorem ModularRealization.formL_second_derivative_upper {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (hz : ∀ j < 2, iteratedDeriv j (mellin m.imaginaryFunction) 1 = 0) :
    iteratedDeriv 2 m.formL 1 =
      (2 * Real.pi / Real.sqrt m.level : ℂ) *
        ((1 + (m.rootNumber : ℂ)) * ∫ t : ℝ in Ioi 1, Real.log t ^ 2 • m.imaginaryFunction t) := by
  rw [m.formL_iteratedDeriv_of_lower_mellin_zero 2 hz, m.mellin_second_derivative_upper]

end VerifiedLcalc.Modularity
