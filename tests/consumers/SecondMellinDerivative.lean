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

run_cmd do
  for declaration in [``VerifiedLcalc.Numerics.mellin_second_derivative_of_rpow,
      ``ModularRealization.mellin_second_derivative,
      ``ModularRealization.mellin_second_derivative_upper] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected second Mellin derivative axiom: {axiomName}"
