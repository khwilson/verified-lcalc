import VerifiedLcalc.Certificate.Support.SpecialValue
import Lean

/-! # Check the special-value contract import -/

open VerifiedLcalc Lean Elab Command

example : Type := SpecialLValueClaim
example (curve : WeierstrassCurve ℤ) : Type := SpecialLValueFacts curve

run_cmd do
  let imported := (← getEnv).allImportedModuleNames
  for backend in [`VerifiedLcalc.Verification.SpecialValue,
      `VerifiedLcalc.Tactic.CertifyEC] do
    if imported.contains backend then
      throwError "Special-value contract imported backend module {backend}"
