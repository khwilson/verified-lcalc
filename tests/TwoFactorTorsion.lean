import VerifiedLcalc.Certification.CurveData
import VerifiedLcalc.EllipticCurve.TorsionBound
import VerifiedLcalc.EllipticCurve.TwoFactorTorsion
import Lean

/-!
# Two-factor torsion on 120.b4

The equation and generator coordinates come from
`data/lmfdb/raw/curvedata-first-1200.txt`. The dependent control uses the
double of the supplied point of order four.
-/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

private def curve120 : WeierstrassCurve ℤ := ⟨0, 1, 0, -20, 0⟩

private instance : (curve120.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

private def p120 : (curve120.baseChange ℚ).toAffine.Point := .mk (x := 0) (y := 0) (by
  rw [WeierstrassCurve.Affine.equation_iff]
  decide +kernel)

private def q120 : (curve120.baseChange ℚ).toAffine.Point := .mk (x := -2) (y := 6) (by
  rw [WeierstrassCurve.Affine.equation_iff]
  decide +kernel)

private def dependent120 : (curve120.baseChange ℚ).toAffine.Point := .mk (x := 4) (y := 0) (by
  rw [WeierstrassCurve.Affine.equation_iff]
  decide +kernel)

example : computePointCount curve120 7 = 8 := by decide +kernel
example : computePointCount curve120 11 = 16 := by decide +kernel

private theorem hP : addOrderOf p120 = 2 :=
  EllipticWitness.exactOrderCheck_sound (by decide +kernel)

private theorem hQ : addOrderOf q120 = 4 :=
  EllipticWitness.exactOrderCheck_sound (by decide +kernel)

private theorem product120 :
    ∃ e : ZMod 2 × ZMod 4 ≃+ AddCommGroup.torsion (curve120.baseChange ℚ).toAffine.Point,
      (e (1, 0) : (curve120.baseChange ℚ).toAffine.Point) = p120 ∧
      (e (0, 1) : (curve120.baseChange ℚ).toAffine.Point) = q120 :=
  exists_torsion_addEquiv_two_factor (by decide) hP hQ
    (outsideCyclicCheck_sound (by decide) hQ (by decide +kernel))
    (checkTorsionBound_correct curve120 7 11 8 (by decide +kernel)).1

example : Nat.card (AddCommGroup.torsion (curve120.baseChange ℚ).toAffine.Point) = 8 := by
  obtain ⟨e, -, -⟩ := product120
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]

example : addOrderOf dependent120 = 2 :=
  EllipticWitness.exactOrderCheck_sound (by decide +kernel)

example : 2 • q120 = dependent120 := by decide +kernel
example : outsideCyclicCheck dependent120 q120 4 = false := by decide +kernel

run_cmd do
  for ax in ← liftTermElabM <| Lean.collectAxioms ``product120 do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected product torsion certificate axiom: {ax}"
