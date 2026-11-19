import CertifiedCurves
import Lean

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- These are new theorems obtained solely from imported .olean declarations.
theorem imported_rank_zero :
    analyticOrderAt (Assumptions.modularWitness DirectCurve.curve DirectCurve.nonsingular).formL
      (1 : ℂ) = 0 := DirectCurve.analytic_rank

theorem imported_rank_one :
    analyticOrderAt (Assumptions.modularWitness Curve37.curve Curve37.nonsingular).formL
      (1 : ℂ) = 1 := Curve37.analytic_rank

theorem imported_wild_rank_one :
    analyticOrderAt (Assumptions.modularWitness Curve112.curve Curve112.nonsingular).formL
      (1 : ℂ) = 1 := Curve112.analytic_rank

-- Failed commands must not leave even their input definitions behind.
meta def expectRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let savedMessages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages := savedMessages }
  unless failed do throwError "An invalid witness was accepted: {name}"
  for suffix in [`witness, `result, `analytic_rank, `certifiedRank] do
    if env.contains (name ++ suffix) then
      throwError "Failed certification leaked {name ++ suffix}"

run_cmd do
  expectRejected `BadCoefficients (← `(certify_ec BadCoefficients from
    EllipticWitness.central { DirectCurve.result with coefficients := [999] }
      DirectCurve.minimality DirectCurve.localData))
  expectRejected `BadTail (← `(certify_ec BadTail from
    EllipticWitness.central { DirectCurve.result with tail := 0 }
      DirectCurve.minimality DirectCurve.localData))
  expectRejected `WrongConductor (← `(certify_ec WrongConductor from
    EllipticWitness.central { DirectCurve.result with conductor := 37 }
      DirectCurve.minimality DirectCurve.localData))
  expectRejected `BadMinimality (← `(certify_ec BadMinimality from
    EllipticWitness.central DirectCurve.result ⟨[]⟩ DirectCurve.localData))
  expectRejected `BadJSON (← `(certify_ec BadJSON from_json_string "{}"))
  expectRejected `BadSchema (← `(certify_ec BadSchema from_json_string
    "{\"schema\":\"not-supported\"}"))

-- A previous failed command must not poison subsequent command elaboration.
certify_ec AfterFailure from EllipticWitness.central
  DirectCurve.result DirectCurve.minimality DirectCurve.localData

run_cmd do
  for name in [`Curve11, `Curve37, `Curve112, `DirectCurve, `AfterFailure] do
    for suffix in [`witness_eq, `nonsingular, `minimality_valid, `local_data_valid,
        `conductor_valid, `root_number_valid, `payload_correct, `excludes_zero,
        `analytic_rank, `curve_analytic_rank] do
      let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ suffix)
      for axiomName in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName ||
            ([`analytic_rank, `curve_analytic_rank].contains suffix &&
              axiomName == ``Assumptions.ellipticModularity) do
          throwError "Unexpected axiom in {name ++ suffix}: {axiomName}"

#eval Curve11.certifiedRank.val
#eval Curve37.certifiedRank.val
#eval Curve112.certifiedRank.val
