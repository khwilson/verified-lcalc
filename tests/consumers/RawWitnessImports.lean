import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
import Lean

/-! Check what Lean loads to read a raw `certify_ec` input, including its rank bounds. -/

open Lean Elab Command

run_cmd do
  let modules := (← getEnv).allImportedModuleNames
  let witnesses := `VerifiedLcalc.Certificate.Witnesses
  -- These records describe verified outputs. Importing them used to load modularity,
  -- regulator and torsion theory solely to read the corresponding optional inputs.
  let checked := [witnesses ++ `EllipticCertificate, witnesses ++ `SpecialValue,
    witnesses ++ `Regulator, witnesses ++ `Torsion, witnesses ++ `IntegralPoints]
  for mod in modules do
    if checked.contains mod then
      throwError "raw curve input pulled in checked-output module {mod}"
    if (`VerifiedLcalc).isPrefixOf mod && !witnesses.isPrefixOf mod then
      throwError "raw curve input pulled in project implementation {mod}"
