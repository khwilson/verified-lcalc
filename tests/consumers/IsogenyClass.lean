/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.IsogenyClass
import Lean

/-! Compiled reuse of the isogeny class facts and exact raw input checks. -/

open VerifiedLcalc TauCeti Lean Elab Command VerifiedLcalcTests.IsogenyClass37

example (h : Exhaustive) :
    IsLeast (Set.range fun φ : Isogeny (source.baseChange ℚ).toAffine
      (source.baseChange ℚ).toAffine => φ.degree) 1 :=
  (model h).toFacts.isLeast_inputDegree (model h).curveIndex

example (h : Exhaustive) :
    (model h).toFacts.classSize = 1 ∧ (model h).toFacts.classDegree = 1 ∧
      (model h).toFacts.matrixRows = [[1]] ∧ (model h).toFacts.isogenyDegrees = {1} :=
  ⟨rfl, rfl, rfl, rfl⟩

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

example : Class37.certificate.isogenyClass =
    some ⟨Class37.isogeny_class, some Class37.isogeny_matrix_order⟩ := rfl

example : Class37.isogeny_class.classSize = Class37.claimed_class_size :=
  Class37.class_size

example : Class37.isogeny_class.classDegree = Class37.claimed_class_deg :=
  Class37.class_deg

example : Class37.isogeny_class.matrixRows = Class37.claimed_isogeny_matrix :=
  Class37.isogeny_matrix

example : Class37.isogeny_class.isogenyDegrees = Class37.claimed_isogeny_degrees.toFinset :=
  Class37.isogeny_degrees

example : Size37.certificate.isogenyClass = some ⟨Size37.isogeny_class, none⟩ := rfl
example : Size37.isogeny_class.classSize = Size37.claimed_class_size := Size37.class_size

end

certify_ec ClassWithoutProof from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"class_size":1,"class_deg":1,
     "isogeny_matrix":[[1]],"isogeny_degrees":[1]}"#

example : ClassWithoutProof.certificate.isogenyClass = none := rfl
example : ClassWithoutProof.witness.isogenyMatrix = some [[1]] :=
  ClassWithoutProof.isogeny_matrix_input_eq

certify_ec ClassesOmitted from { equation := source }

example : ClassesOmitted.witness.classSize = none := rfl
example : ClassesOmitted.certificate.isogenyClass = none := rfl

private meta def rejectClass (base : Name) (command : Syntax)
    (expected : Option String := none) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch err =>
    if let some label := expected then
      let message ← err.toMessageData.toString
      unless (message.splitOn s!"failed checking {base}.{label}").length > 1 do
        throwError "Expected {base}.{label} to fail its check, got {message}"
    failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Wrong isogeny class accepted: {base}"
  for suffix in [`curve, `witness, `claimed_class_size, `class_size, `class_deg,
      `isogeny_class_evidence, `isogeny_class, `isogeny_matrix_order, `certificate] do
    if env.contains (base ++ suffix) then throwError "Rejected class leaked {base ++ suffix}"

run_cmd do
  let env ← getEnv
  for suffix in [`class_size, `class_deg, `isogeny_matrix, `isogeny_degrees] do
    if env.contains (`ClassWithoutProof ++ suffix) then
      throwError "Missing class evidence emitted an assertion for {suffix}"
  rejectClass `BadSize (← `(certify_ec BadSize from { equation := source, classSize := some 0 }))
  rejectClass `BadDegree (← `(certify_ec BadDegree from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"class_deg":1.5}"#))
  rejectClass `RaggedMatrix (← `(certify_ec RaggedMatrix from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"isogeny_matrix":[[1,2],[1]]}"#))
  rejectClass `DuplicateDegrees (← `(certify_ec DuplicateDegrees from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"isogeny_degrees":[1,1]}"#))
  for declaration in [``IsogenyClassModel.toFacts, ``IsogenyClassFacts.isLeast_inputDegree,
      ``model, ``ordering, ``ClassWithoutProof.certificate, ``Class37.certificate,
      ``Class37.class_size, ``Class37.class_deg, ``Class37.isogeny_matrix,
      ``Class37.isogeny_degrees] do
    for assumption in ← liftTermElabM (Lean.collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected rational isogeny class axiom: {assumption}"

section

variable {E : WeierstrassCurve ℚ} [h : SingletonModel E]

run_cmd do
  rejectClass `WrongSize (← `(certify_ec WrongSize from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"class_size":2}"#
      with_proofs (proofAttachment h.complete))) (some "class_size")
  rejectClass `WrongClassDegree (← `(certify_ec WrongClassDegree from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"class_deg":2}"#
      with_proofs (proofAttachment h.complete))) (some "class_deg")
  rejectClass `WrongMatrix (← `(certify_ec WrongMatrix from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"isogeny_matrix":[[2]]}"#
      with_proofs (proofAttachment h.complete))) (some "isogeny_matrix")
  rejectClass `WrongDegrees (← `(certify_ec WrongDegrees from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"isogeny_degrees":[2]}"#
      with_proofs (proofAttachment h.complete))) (some "isogeny_degrees")

end
