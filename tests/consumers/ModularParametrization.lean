/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.ModularParametrization
import Lean

/-! Reuse the minimum modular map and the exact verified producer values. -/

open VerifiedLcalc VerifiedLcalc.Modularity VerifiedLcalcTests.ModularParametrization11
open TauCeti.WorkedExamples Lean Elab Command

section

variable {level : ℕ} [h : GeometricModel11 level]

private noncomputable def checked11 : CertifiedModularParametrization curve11a2 :=
  Modular11.certificate.modularParametrization.get (by rfl)

example : (checked11.degree.get (by rfl)).val = 1 := rfl
example : (checked11.maninConstant.get (by rfl)).val = 1 := rfl
example : (checked11.optimality.get (by rfl)).val = 1 := rfl

example : letI : NeZero checked11.evidence.realization.level :=
      ⟨Nat.ne_of_gt checked11.evidence.realization.positiveLevel⟩
    checked11.evidence.pullback.degree = 1 :=
  checked11.evidence.degree_eq

example : letI : NeZero checked11.evidence.realization.level :=
      ⟨Nat.ne_of_gt checked11.evidence.realization.positiveLevel⟩
    checked11.evidence.pullback.PullsBackDifferential checked11.evidence.realization.form 1 :=
  checked11.evidence.differential

example : gammaZeroDifferentialPeriods checked11.evidence.realization.form 1 =
    ((curve11a2.baseChange ℚ).map (Rat.castHom ℂ)).periodLattice.toAddSubgroup := by
  let status := checked11.evidence.optimal.get (by rfl)
  exact status.property.mpr rfl

certify_ec Ambiguous from ({ equation := curve11a2, optimality := some 3 } : EllipticWitness)
  with_proofs (proofs h)

example : Ambiguous.witness.optimality = some 3 := rfl

example : (Ambiguous.certificate.modularParametrization.get (by rfl)).optimality = none := rfl

certify_ec VerifiedLean from
  ({ equation := curve11a2, optimality := some 1, maninConstant := some 1 } : EllipticWitness)
  with_proofs (proofs h)

example : (VerifiedLean.certificate.modularParametrization.get (by rfl)).degree = none := rfl

example : (VerifiedLean.certificate.modularParametrization.get (by rfl)).maninConstant.isSome =
    true := rfl

end

-- Actual LMFDB 11.a3 values without a proof of its degree-five modular map.
certify_ec ReportOnly from_json_string
  r#"{"ainvs":[0,-1,1,0,0],"degree":5,"manin_constant":5,"optimality":0}"#

example : ReportOnly.witness.maninConstant = some 5 := rfl

example : ReportOnly.certificate.modularParametrization = none := rfl

private meta def rejectClaim (base : Name) (cmd : Syntax) (field : Name) :
    CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand cmd
    failed := (← get).messages.hasErrors
  catch err =>
    let msg ← err.toMessageData.toString
    unless (msg.splitOn s!"failed checking {base}.{field}").length > 1 do
      throwError "Expected {base}.{field} to fail, got {msg}"
    failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Bad modular claim accepted for {base}"
  for suffix in [`curve, `witness, `modular_parametrization_evidence, `modular_parametrization_fact,
      `modular_degree, `manin_constant, `optimality, `certificate] do
    if env.contains (base ++ suffix) then
      throwError "Rejected modular claim leaked {base ++ suffix}"

section

variable {level : ℕ} [h : GeometricModel11 level]

run_cmd do
  rejectClaim `BadManin (← `(certify_ec BadManin from_json_string
    r#"{"ainvs":[0,-1,1,-10,-20],"degree":1,"manin_constant":5,"optimality":1}"#
    with_proofs (proofs h))) `manin_constant
  rejectClaim `BadOptimality (← `(certify_ec BadOptimality from
    ({ equation := curve11a2, optimality := some 0, maninConstant := some 1 } : EllipticWitness)
    with_proofs (proofs h))) `optimality
  rejectClaim `BadDegree (← `(certify_ec BadDegree from
    ({ equation := curve11a2, modularDegree := some 5 } : EllipticWitness)
    with_proofs (proofs h))) `modular_degree
  let env ← getEnv
  if env.contains `Ambiguous.optimality then
    throwError "Ambiguous producer metadata emitted an optimality claim"
  for name in [``Modular11.modular_degree, ``Modular11.manin_constant,
      ``Modular11.optimality, ``Modular11.certificate, ``VerifiedLean.certificate] do
    for ax in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

end
