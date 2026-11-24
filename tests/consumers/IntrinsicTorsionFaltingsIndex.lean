/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.IntrinsicTorsionFaltingsIndex
import Lean

/-! Reuse the compiled intrinsic torsion and Faltings index proofs. -/

open VerifiedLcalc VerifiedLcalcTests.IsogenyClass37
open VerifiedLcalcTests.IntrinsicTorsionFaltingsIndex37
open Lean Elab Command

example : Intrinsic37.certificate.intrinsicTorsion = some Intrinsic37.intrinsic_torsion_fact := rfl

example : (Intrinsic37.certificate.intrinsicTorsion.get (by rfl)).reported =
    Intrinsic37.claimed_intrinsic_torsion := rfl

example {A : Type*} [AddCommGroup A]
    (pairing : AddCommGroup.torsion (Intrinsic37.curve.baseChange ℚ).toAffine.Point →+
      (AddCommGroup.torsion (Intrinsic37.curve.baseChange ℚ).toAffine.Point →+ A)) :
    Nat.card pairing.ker = 1 :=
  (Intrinsic37.certificate.intrinsicTorsion.get (by rfl)).card_radical pairing

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

example : Index37.certificate.faltingsIndex = some (indexFact h.complete) := rfl

example : (Index37.certificate.faltingsIndex.get (by rfl)).index = 0 :=
  Index37.faltings_index

end

-- With three equal heights, index 0
-- precedes index 1, and the tied index 1 never precedes index 0.
example : faltingsPrecedes (fun _ : Fin 3 => (2 : ℝ)) 0 1 ∧
    ¬ faltingsPrecedes (fun _ : Fin 3 => (2 : ℝ)) 1 0 := by
  simp [faltingsPrecedes]

certify_ec Bare from ({
  equation := source
  intrinsicTorsion := some 1
  faltingsIndex := some 0 } : EllipticWitness)

example : Bare.certificate.intrinsicTorsion = none ∧ Bare.certificate.faltingsIndex = none :=
  ⟨rfl, rfl⟩

certify_ec NontrivialTorsion from_json_string
  r#"{"ainvs":[0,0,0,-1,0],"torsion":4,"torsion_structure":[2,2],"intrinsic_torsion":1,
      "torsion_generators":[[0,0,1],[-1,0,1],[1,0,1]],"torsion_generator_orders":[2,2,2],
      "torsion_bound":{"first_prime":3,"second_prime":5,"bound":4}}"#

example : Nat.card (AddCommGroup.torsion (NontrivialTorsion.curve.baseChange ℚ).toAffine.Point) =
    4 := NontrivialTorsion.torsion

example : NontrivialTorsion.certificate.intrinsicTorsion = none := rfl

private meta def rejectClaim (base : Name) (cmd : Syntax) (label : String) :
    CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand cmd
    failed := (← get).messages.hasErrors
  catch err =>
    let msg ← err.toMessageData.toString
    unless (msg.splitOn s!"failed checking {base}.{label}").length > 1 do
      throwError "Expected {base}.{label} to fail, got {msg}"
    failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Bad catalogue claim accepted for {base}"
  for suffix in [`curve, `witness, `intrinsic_torsion_fact, `faltings_index_fact, `certificate] do
    if env.contains (base ++ suffix) then
      throwError "Rejected catalogue claim leaked {base ++ suffix}"

run_cmd do
  rejectClaim `BadIntrinsic (← `(certify_ec BadIntrinsic from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"intrinsic_torsion":2,
        "torsion_bound":{"first_prime":3,"second_prime":5,"bound":1}}"#))
    "intrinsic_torsion_value"

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

run_cmd do
  rejectClaim `BadIndex (← `(certify_ec BadIndex from
    ({ equation := source, faltingsIndex := some 1 } : EllipticWitness)
    with_proofs (withIndex h.complete))) "faltings_index"
  let env ← getEnv
  for field in [`intrinsic_torsion, `faltings_index] do
    if env.contains (`Bare ++ field) then throwError "A bare claim produced {field}"
  for name in [``IntrinsicTorsionFact.card_radical, ``FaltingsIndexFact.index_eq_card_filter,
      ``Intrinsic37.intrinsic_torsion, ``Intrinsic37.certificate,
      ``Index37.faltings_index, ``Index37.certificate] do
    for ax in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected intrinsic torsion or Faltings index axiom: {ax}"

end
