import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
import Lean

/-! Check what Lean loads to read a raw `certify_ec` input, including its rank bounds. -/

open Lean Elab Command

run_cmd do
  let modules := (← getEnv).allImportedModuleNames
  let witnesses := `VerifiedLcalc.Certificate.Witnesses
  for mod in modules do
    if (`TauCeti).isPrefixOf mod then
      throwError "raw curve input pulled in TauCeti module {mod}"
    if (`VerifiedLcalc).isPrefixOf mod && !witnesses.isPrefixOf mod then
      throwError "raw curve input pulled in project implementation {mod}"
