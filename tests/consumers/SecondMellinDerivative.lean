import VerifiedLcalc.EllipticCurve.Modularity.SecondDerivative
import Lean

/-! # Reuse the compiled second Mellin moment and check its axiom dependencies -/

open Lean Elab Command MeasureTheory Set VerifiedLcalc.Modularity

example {e : WeierstrassCurve ℤ} (m : ModularRealization e) (h : m.rootNumber = -1) :
    iteratedDeriv 2 (mellin m.imaginaryFunction) 1 = 0 := by
  rw [m.mellin_second_derivative_upper, h]
  simp

example {e : WeierstrassCurve ℤ} (m : ModularRealization e) (h : m.rootNumber = 1) :
    iteratedDeriv 2 (mellin m.imaginaryFunction) 1 =
      2 * ∫ t : ℝ in Ioi 1, Real.log t ^ 2 • m.imaginaryFunction t := by
  rw [m.mellin_second_derivative_upper, h]
  norm_num

example {e : WeierstrassCurve ℤ} (m : ModularRealization e) (h : m.rootNumber = 1) :
    iteratedDeriv 3 (mellin m.imaginaryFunction) 1 = 0 := by
  rw [m.mellin_iterated_derivative_upper, h]
  norm_num

example {e : WeierstrassCurve ℤ} (m : ModularRealization e)
    (hz : ∀ j < 2, iteratedDeriv j (mellin m.imaginaryFunction) 1 = 0) (h : m.rootNumber = 1) :
    iteratedDeriv 2 m.formL 1 =
      (2 * Real.pi / Real.sqrt m.level : ℂ) *
        (2 * ∫ t : ℝ in Ioi 1, Real.log t ^ 2 • m.imaginaryFunction t) := by
  rw [m.formL_second_derivative_upper hz, h]
  norm_num

run_cmd do
  for declaration in [``VerifiedLcalc.Numerics.mellin_iteratedDeriv_of_isBigO_rpow,
      ``ModularRealization.mellin_second_derivative,
      ``ModularRealization.mellin_second_derivative_upper,
      ``ModularRealization.mellin_iterated_derivative_upper,
      ``ModularRealization.formL_iteratedDeriv_of_lower_mellin_zero,
      ``ModularRealization.formL_second_derivative_upper] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected second Mellin derivative axiom: {axiomName}"
