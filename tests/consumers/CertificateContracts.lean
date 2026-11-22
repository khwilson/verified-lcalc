import VerifiedLcalc.Certificates
import Lean

/-! This consumer checks the public data contracts without importing certification backends. -/

open VerifiedLcalc Lean Elab Command

#check IntegralXSupport
#check CompleteIntegralPointFacts
#check DegreeTwoIsogenyFact
#check TorsionBoundWitness
#check TorsionDivisorFacts
#check CyclicTorsionFacts
#check TwoFactorTorsionFacts
#check TorsionPrimeSupportFacts
#check TorsionFacts

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
