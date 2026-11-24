import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
import Lean

/-! Check what Lean loads to read a raw `certify_ec` input, including its optional claims. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let witnesses := `VerifiedLcalc.Certificate.Witnesses
  -- These records describe verified outputs. Importing them used to load modularity,
  -- regulator and torsion theory solely to read the corresponding optional inputs.
  for output in [`VerifiedLcalc.EllipticCertificate, `VerifiedLcalc.SpecialLValueFacts,
      `VerifiedLcalc.RegulatorFacts, `VerifiedLcalc.TorsionWitness,
      `VerifiedLcalc.CompleteIntegralPointFacts] do
    if env.contains output then
      throwError "raw curve input pulled in checked output {output}"
  -- The pinned Mathlib equation has no Repr or DecidableEq. Inline derivation for
  -- the raw equation record needs the isolated adapter for these two instances.
  let equationInstances := `VerifiedLcalc.Certificate.Support.WeierstrassInstances
  for mod in modules do
    if (`VerifiedLcalc).isPrefixOf mod && !witnesses.isPrefixOf mod && mod != equationInstances then
      throwError "raw curve input pulled in project implementation {mod}"
