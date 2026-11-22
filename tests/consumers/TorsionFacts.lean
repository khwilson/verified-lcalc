import VerifiedLcalc.Certificates.TorsionFacts
import Lean

/-! The public torsion data import without the checker or proof adapter. -/

open VerifiedLcalc Lean Elab Command

#check TorsionBoundWitness
#check TorsionDivisorFacts
#check CyclicTorsionFacts
#check TwoFactorTorsionFacts
#check TorsionPrimeSupportFacts
#check TorsionFacts

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for backend in [`VerifiedLcalc.Certification.TorsionBoundFacts,
    `VerifiedLcalc.EllipticCurve.TorsionBound] do
    if imported.contains backend then
      throwError m!"torsion contract imported backend module {backend}"
