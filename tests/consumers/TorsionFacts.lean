import VerifiedLcalc.Certificates.TorsionFacts
import Lean

/-! The public torsion data import without the checker or proof adapter. -/

open VerifiedLcalc Lean Elab Command

example : Type := TorsionBoundWitness
example (curve : WeierstrassCurve ℤ) : Type := TorsionDivisorFacts curve
example (curve : WeierstrassCurve ℤ) : Type := CyclicTorsionFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TwoFactorTorsionFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionPrimeSupportFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionFacts curve

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for backend in [`VerifiedLcalc.Certification.TorsionBoundFacts,
    `VerifiedLcalc.EllipticCurve.TorsionBound] do
    if imported.contains backend then
      throwError m!"torsion contract imported backend module {backend}"
