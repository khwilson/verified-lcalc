import VerifiedLcalcTests.Fixtures.DegreeTwoIsogeny
import VerifiedLcalc.Tactic.CertifyEC
import Lean

/-! # Compiled reuse and axiom audit of the minimum rational isogeny degree -/

open Lean Elab Command TauCeti VerifiedLcalc VerifiedLcalcTests.Isogeny112

example : edge.isogeny.degree = 2 :=
  edge.degree_eq

example (φ : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine) :
    2 ≤ φ.degree :=
  edge.degree_le φ

example : IsLeast (Set.range fun φ :
    Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine => φ.degree) 2 :=
  edge.isLeast_degree

example : letI := edge.source_elliptic
    IsAddCyclic edge.isogeny.ker :=
  edge.kernel_cyclic

example : ¬ Nonempty (DegreeTwoIsogenyFact source source) := by
  rintro ⟨wrong⟩
  have h := wrong.degree_le (Isogeny.id (source.baseChange ℚ).toAffine)
  simp at h

certify_ec Edge112 from_json_string
  r#"{"ainvs":[0,1,0,0,4],"isogeny_edge":{"target":{"ainvs":[0,1,0,-40,84]},"degree":2}}"#
  with_isogeny edge

example : Edge112.degree_two_isogeny.isogeny.degree = 2 :=
  Edge112.degree_two_isogeny.degree_eq

certify_ec RawEdge112 from_json_string
  r#"{"ainvs":[0,1,0,0,4],"lmfdb_label":"112.a2","isogeny_edge":{
      "target":{"ainvs":[0,1,0,-40,84],"lmfdb_label":"112.a1"},"degree":2,"kernel_x":-2}}"#

example : RawEdge112.degree_two_isogeny.isogeny.degree = RawEdge112.claimed_isogeny_edge.degree :=
  RawEdge112.isogeny_degree

example :
    Edge112.certificate.isogeny =
      some ⟨Edge112.isogeny_target, Edge112.degree_two_isogeny⟩ := rfl

example :
    RawEdge112.certificate.isogeny =
      some ⟨RawEdge112.isogeny_target, RawEdge112.degree_two_isogeny⟩ := rfl

private meta def rejectEdge (base : Name) (command : Syntax) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Wrong isogeny accepted: {base}"
  for suffix in [`curve, `witness, `isogeny_target, `degree_two_isogeny,
      `isogeny_minimum_degree, `certificate] do
    if env.contains (base ++ suffix) then throwError "Rejected isogeny leaked {base ++ suffix}"

run_cmd do
  rejectEdge `WrongEdgeTarget (← `(certify_ec WrongEdgeTarget from
    { equation := source, isogenyEdge := some ⟨source, 2, none⟩ } with_isogeny edge))
  rejectEdge `WrongEdgeSource (← `(certify_ec WrongEdgeSource from
    { equation := target, isogenyEdge := some ⟨target, 2, none⟩ } with_isogeny edge))
  rejectEdge `WrongEdgeDegree (← `(certify_ec WrongEdgeDegree from
    { equation := source, isogenyEdge := some ⟨target, 3, some (-2)⟩ }))
  rejectEdge `WrongRawKernel (← `(certify_ec WrongRawKernel from
    { equation := source, isogenyEdge := some ⟨target, 2, some 0⟩ }))
  rejectEdge `MissingEdgeProof (← `(certify_ec MissingEdgeProof from
    { equation := source, isogenyEdge := some ⟨target, 2, none⟩ }))
  let declarations := [``edge, ``DegreeTwoIsogenyFact.ofVelu, ``DegreeTwoIsogenyFact.isLeast_degree,
    ``Edge112.certificate, ``Edge112.isogeny_minimum_degree, ``RawEdge112.isogeny_minimum_degree]
  for name in declarations do
    for assumption in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected rational isogeny axiom: {assumption}"
