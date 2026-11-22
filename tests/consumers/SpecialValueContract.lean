import VerifiedLcalc.Certificates
import Lean

/-! # Check the special-value contract import -/

open VerifiedLcalc Lean Elab Command

example : Type := SpecialLValueClaim
example (curve : WeierstrassCurve ℤ) : Type := SpecialLValueFacts curve

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for backend in [`VerifiedLcalc.Certification.SpecialValue,
      `VerifiedLcalc.Tactic.CertifyEC] do
    if imported.contains backend then
      throwError "Contract umbrella imported backend module {backend}"
