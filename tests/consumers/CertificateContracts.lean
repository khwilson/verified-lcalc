import VerifiedLcalc.Certificates
import Lean

/-! This consumer checks the public data contracts without importing certification backends. -/

open VerifiedLcalc Lean Elab Command

example (curve : WeierstrassCurve ℤ) : Type := IntegralXSupport curve
example (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] :
    Type := CompleteIntegralPointFacts curve
example (source target : WeierstrassCurve ℤ) : Type := DegreeTwoIsogenyFact source target
example : Type := TorsionBoundWitness
example (curve : WeierstrassCurve ℤ) : Type := TorsionDivisorFacts curve
example (curve : WeierstrassCurve ℤ) : Type := CyclicTorsionFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TwoFactorTorsionFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionPrimeSupportFacts curve
example (curve : WeierstrassCurve ℤ) : Type := TorsionFacts curve

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for backend in [`VerifiedLcalc.Certification.CurveData,
    `VerifiedLcalc.Certification.IntegralPointCount,
    `VerifiedLcalc.Certification.DegreeTwoIsogeny,
    `VerifiedLcalc.Certification.DegreeTwoIsogenyRaw,
    `VerifiedLcalc.Certification.TorsionBoundFacts,
    `VerifiedLcalc.EllipticCurve.TorsionBound] do
    if imported.contains backend then
      throwError m!"contract umbrella imported backend module {backend}"
