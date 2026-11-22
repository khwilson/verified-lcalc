import CertifiedCurves.Invariants
import Lean

/-! Regression tests for stored invariant checks through `certify_ec`. -/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.EllipticCurve

-- Native LMFDB rational pairs, canonical strings, exact integer literals, and
-- partial data all feed the same witness. Missing prerequisites emit no claim.
certify_ec Partial37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"jinv":[110592,37],"signD":1,"absD":37,
      "bad_primes":[37],"num_bad_primes":1,"semistable":true,"squarefree_disc":true,
      "local_invariants":[{"prime":37,"discriminant_valuation":1,
        "j_denominator_valuation":1,"reduction_type":-1}],
      "conductor":37,"global_root_number":-1,"anlist":[0,1,-2,-3]}"#
example : (Partial37.curve.baseChange ℚ).j = 110592 / 37 := Partial37.j_invariant

certify_ec JZero from_json_string
  r#"{"ainvs":[0,0,0,0,1],"jinv":"0","signD":-1,"discriminant":-432}"#
certify_ec IntegralJ from { equation := ⟨0, 0, 0, 0, 1⟩, jIntegral := some true }
example : IsLocalization.IsInteger ℤ (IntegralJ.curve.baseChange ℚ).j :=
  IntegralJ.j_integral.mpr rfl

certify_ec NonintegralJ from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"j_integral":false}"#
example : ¬ IsLocalization.IsInteger ℤ (NonintegralJ.curve.baseChange ℚ).j :=
  fun h => Bool.false_ne_true (NonintegralJ.j_integral.mp h)

certify_ec PotentialGood from
  { equation := ⟨0, 0, 0, 0, 1⟩, potentialGoodReduction := some true }
example : EllipticCurve.HasEverywherePotentialGoodReduction (PotentialGood.curve.baseChange ℚ) :=
  PotentialGood.potential_good_reduction.mpr rfl

certify_ec NoPotentialGood from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"potential_good_reduction":false}"#
example :
    ¬ EllipticCurve.HasEverywherePotentialGoodReduction (NoPotentialGood.curve.baseChange ℚ) :=
  fun h => Bool.false_ne_true (NoPotentialGood.potential_good_reduction.mp h)
example : NoPotentialGood.witness.jIntegral = none := rfl

certify_ec J1728 from_json_string
  r#"{"ainvs":[0,0,0,-1,0],"jinv":"1728/1","binvs":[0,-2,0,-1],"cinvs":[48,0]}"#

-- A local table's root_number must never become a global-root claim.
certify_ec LocalSignMetadata from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"prime":37,"root_number":1,"minimality":[37],
      "local_data":{"at_two":null,"at_three":null}}"#
example : LocalSignMetadata.witness.rootNumber = none := rfl

certify_ec JSON37 from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"jinv":["110592","37"],"binvs":[0,-2,1,-1],"cinvs":[48,-216],
      "absD":37,"bad_primes":[37],"num_bad_primes":1,"semistable":true,"squarefree_disc":true,
      "local_invariants":[{"prime":37,"discriminant_valuation":1,
        "j_denominator_valuation":1,"reduction_type":-1}],
      "conductor":37,"global_root_number":-1,"anlist":[0,1,-2,-3,2,-2,6,-1,0],
      "minimality":[37],"local_data":{"at_two":null,"at_three":null}}"#
example : JSON37.curve.Δ.natAbs = 37 := JSON37.minimal_discriminant_abs.2

example : WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (JSON37.curve.baseChange ℚ) := JSON37.semistable.mpr rfl

certify_ec AdditiveLocal from_json_string
  r#"{"ainvs":[0,0,0,0,1],"minimality":[2,2,2,2,3,3,3],"semistable":false,
      "squarefree_disc":false,"prime":3,"discriminant_valuation":3,
      "j_denominator_valuation":0,"reduction_type":0}"#

example : ¬ WeierstrassCurve.IsSemistable (NumberField.RingOfIntegers ℚ)
    (AdditiveLocal.curve.baseChange ℚ) := fun h => by
  have := AdditiveLocal.semistable.mp h
  contradiction

certify_ec SplitLocal from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"minimality":[11,11,11,11,11],
      "local_invariants":[{"prime":11,"reduction_type":1}]}"#

run_cmd do
  let input ← CertifyEC.jsonInput
    r#"{"ainvs":[0,0,1,-1,0],"jinv":[110592,37]}"#
  CertifyEC.certifyAtomic `ProgrammaticInvariant input

meta def invariantRejected (name : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Incorrect invariant accepted: {name}"
  for suffix in [`witness, `curve, `nonsingular, `j_invariant, `discriminant,
      `claimed_j_invariant, `claimed_j_integral, `j_integral, `j_integral_input_eq,
      `j_integral_value_valid, `claimed_discriminant, `global_minimal,
      `claimed_potential_good_reduction, `potential_good_reduction,
      `potential_good_reduction_input_eq, `potential_good_reduction_value_valid,
      `minimal_discriminant_abs, `conductor, `root_number, `dirichlet_coefficients,
      `bad_primes, `bad_reduction_primes, `num_bad_primes,
      `semistable, `squarefree_discriminant, `local_invariants, `claimed_semistable,
      `claimed_squarefree_discriminant, `claimed_local_invariants] do
    if env.contains (name ++ suffix) then throwError "Rejected invariant leaked {name ++ suffix}"

run_cmd do
  invariantRejected `WrongJ (← `(certify_ec WrongJ from
    { Invariants37.witness with jInvariant := some 0 }))
  invariantRejected `WrongIntegralJ (← `(certify_ec WrongIntegralJ from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"j_integral":true}"#))
  invariantRejected `WrongNonintegralJ (← `(certify_ec WrongNonintegralJ from
    { IntegralJ.witness with jIntegral := some false }))
  invariantRejected `WrongPotentialGood (← `(certify_ec WrongPotentialGood from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"potential_good_reduction":true}"#))
  invariantRejected `WrongNoPotentialGood (← `(certify_ec WrongNoPotentialGood from
    { PotentialGood.witness with potentialGoodReduction := some false }))
  invariantRejected `WrongDiscriminant (← `(certify_ec WrongDiscriminant from
    { Invariants37.witness with discriminant := some (-37) }))
  invariantRejected `WrongB (← `(certify_ec WrongB from
    { Invariants37.witness with bInvariants := some (0, 0, 0, 0) }))
  invariantRejected `WrongC (← `(certify_ec WrongC from
    { Invariants37.witness with cInvariants := some (48, 216) }))
  invariantRejected `WrongSign (← `(certify_ec WrongSign from
    { Invariants37.witness with discriminantSign := some 0 }))
  invariantRejected `WrongAbsD (← `(certify_ec WrongAbsD from
    { Invariants37.witness with minimalDiscriminantAbs := some 1 }))
  invariantRejected `MissingBadPrime (← `(certify_ec MissingBadPrime from
    { Invariants37.witness with badPrimes := some [] }))
  invariantRejected `DuplicateBadPrime (← `(certify_ec DuplicateBadPrime from
    { Invariants37.witness with badPrimes := some [37, 37] }))
  invariantRejected `WrongBadCount (← `(certify_ec WrongBadCount from
    { Invariants37.witness with numBadPrimes := some 2 }))
  invariantRejected `WrongSemistability (← `(certify_ec WrongSemistability from
    { Invariants37.witness with semistable := some false }))
  invariantRejected `WrongSquarefree (← `(certify_ec WrongSquarefree from
    { Invariants37.witness with squarefreeDiscriminant := some false }))
  invariantRejected `WrongLocalValuation (← `(certify_ec WrongLocalValuation from
    { Invariants37.witness with localInvariants := some [
        { prime := 37, discriminantValuation := some 0 }] }))
  invariantRejected `WrongLocalJValuation (← `(certify_ec WrongLocalJValuation from
    { Invariants37.witness with localInvariants := some [
        { prime := 37, jDenominatorValuation := some 0 }] }))
  invariantRejected `WrongLocalReduction (← `(certify_ec WrongLocalReduction from
    { Invariants37.witness with localInvariants := some [
        { prime := 37, reductionType := some 1 }] }))
  invariantRejected `CompositeLocalPrime (← `(certify_ec CompositeLocalPrime from
    { Invariants37.witness with localInvariants := some [
        { prime := 4, discriminantValuation := some 0 }] }))
  invariantRejected `WrongConductor (← `(certify_ec WrongConductor from
    { Invariants37.witness with conductor := some 1 }))
  invariantRejected `WrongRootNumber (← `(certify_ec WrongRootNumber from
    { Invariants37.witness with rootNumber := some 1 }))
  invariantRejected `WrongAN (← `(certify_ec WrongAN from
    { Invariants37.witness with dirichletCoefficients := some [1, 999] }))
  -- Scaling the equation scales its discriminant; it must not be passed off
  -- as a globally minimal model for an absD certificate.
  invariantRejected `NonminimalAbsD (← `(certify_ec NonminimalAbsD from
    { equation := ⟨0, 0, 8, -16, 0⟩, minimality := some ⟨[2,2,2,2,2,2,2,2,2,2,2,2,37]⟩,
      minimalDiscriminantAbs := some 151552 }))
  for suffix in [`minimal_discriminant_abs, `conductor, `root_number, `dirichlet_coefficients,
      `bad_primes, `bad_reduction_primes, `num_bad_primes,
      `semistable, `squarefree_discriminant, `local_invariants] do
    if (← getEnv).contains (`Partial37 ++ suffix) then
      throwError "Missing arithmetic evidence generated an invariant claim"
  if (← getEnv).contains `NoPotentialGood.j_integral then
    throwError "An omitted j_integral claim generated a theorem"
  if (← getEnv).contains `IntegralJ.potential_good_reduction then
    throwError "An omitted potential_good_reduction claim generated a theorem"
  if (← getEnv).contains `LocalSignMetadata.root_number then
    throwError "Local root metadata became a global sign theorem"

run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in [`IntegralJ.j_integral, `NonintegralJ.j_integral,
      `PotentialGood.potential_good_reduction, `NoPotentialGood.potential_good_reduction] do
    for ax in ← liftTermElabM <| Lean.collectAxioms theoremName do
      unless standard.contains ax do throwError "Unexpected j-invariant check axiom: {ax}"
  for name in [`Invariants37, `JSON37] do
    for rankName in [`analytic_rank, `algebraic_rank_lower_bound] do
      if (← getEnv).contains (name ++ rankName) then
        throwError "Stored arithmetic invariants generated an unsupported rank claim"
    for suffix in [`b_invariants, `c_invariants, `j_invariant, `minimal_discriminant_abs,
        `global_minimal, `dirichlet_coefficients, `bad_primes,
        `bad_reduction_primes, `num_bad_primes, `semistable, `squarefree_discriminant,
        `local_invariants] do
      for ax in ← liftTermElabM <| Lean.collectAxioms (name ++ suffix) do
        unless standard.contains ax do throwError "Unexpected invariant axiom: {ax}"
    for suffix in [`conductor, `root_number] do
      let axioms ← liftTermElabM <| Lean.collectAxioms (name ++ suffix)
      unless axioms.contains ``VerifiedLcalc.Assumptions.ellipticModularity do
        throwError "Conditional arithmetic boundary was not recorded"
      for ax in axioms do
        unless standard.contains ax || ax == ``VerifiedLcalc.Assumptions.ellipticModularity do
          throwError "Unexpected conditional invariant axiom: {ax}"

run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let additiveFields := [`semistable, `squarefree_discriminant, `local_invariants]
  for (name, fields) in [(`AdditiveLocal, additiveFields), (`SplitLocal, [`local_invariants])] do
    for field in fields do
      for ax in ← liftTermElabM <| Lean.collectAxioms (name ++ field) do
        unless standard.contains ax do throwError "Unexpected local invariant axiom: {ax}"

run_cmd do
  for j in ["[1,0]", "[1,-1]", "[1,2,3]", "0.5", "\"0.5\""] do
    match CurveDataJson.parse ("{\"ainvs\":[0,0,1,-1,0],\"jinv\":" ++ j ++ "}") with
    | .error _ => pure ()
    | .ok _ => throwError "Malformed exact rational accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,1,-1,0],"j_integral":"false"}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Non-boolean j_integral accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,1,-1,0],"potential_good_reduction":0}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Non-boolean potential_good_reduction accepted"
  match CurveDataJson.parse r#"{"ainvs":[0,0,1,-1,0],"anlist":[1,1]}"# with
  | .error _ => pure ()
  | .ok _ => throwError "Nonzero anlist origin accepted"
