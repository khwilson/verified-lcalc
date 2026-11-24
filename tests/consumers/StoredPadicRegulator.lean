/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.StoredPadicRegulator

/-! # Imported positive-rank stored regulator checks and atomic rejection -/

open VerifiedLcalc EllipticCurve VerifiedLcalcTests.StoredPadic37 Lean Elab Command

section

variable {model : WeierstrassCurve ℤ} [h : Premises model]

include h in
/-- The imported regulator certificate preserves all five native coordinates. -/
theorem importedStoredPadicCoordinates :
    let fact := Checked.certificate.analytic.storedPadicRegulator.get (by rfl)
    (fact.classLabel, (fact.report.p : ℕ), fact.report.prec, fact.report.val, fact.report.unit) =
      ("37.a", 5, 20, 1, 17009699681281) := rfl

include h in
/-- The imported regulator is nonzero with the reported integer valuation. -/
theorem importedStoredPadicValuation :
    let value := ordinaryPadicHeightAtMultiple h.sigma (21 / 25) (-69 / 125) 5 8
    value ≠ 0 ∧ value.valuation = 1 :=
  (Checked.certificate.analytic.storedPadicRegulator.get (by rfl)).valuation_eq

set_option maxRecDepth 8000 in
-- The exact rational logarithm uses 35 terms.
certify_ec TypedPadic from
  { equation := curve, padicRegulator := some ⟨5, 20, 1, 17009699681281⟩,
    padicRegulatorClassLabel := some "37.a" }
  with_proofs (proofs h)

example : TypedPadic.certificate.analytic.storedPadicRegulator.isSome = true := rfl

set_option maxRecDepth 8000 in
-- The exact rational logarithm uses 35 terms.
certify_ec FlatPadic from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"lmfdb_iso":"37.a","p":5,"prec":20,"val":1,"unit":17009699681281}"#
  with_proofs (proofs h)

example : FlatPadic.certificate.analytic.storedPadicRegulator.isSome = true := rfl

set_option maxRecDepth 8000 in
-- The wrong residue is rejected by the same exact 35-term rational check.
run_cmd do
  let badLabel ← `(certify_ec WrongPadicClass from
    { equation := curve, padicRegulator := some ⟨5, 20, 1, 17009699681281⟩,
      padicRegulatorClassLabel := some "37.b" } with_proofs (proofs h))
  let badUnit ← `(certify_ec WrongPadicUnit from
    { equation := curve, padicRegulator := some ⟨5, 20, 1, 17009699681282⟩,
      padicRegulatorClassLabel := some "37.a" } with_proofs (proofs h))
  let duplicate ← `(certify_ec DuplicatePadic from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"lmfdb_iso":"37.a","p":5,"prec":20,"val":1,"unit":17009699681281,
        "padic_regulator":{"lmfdb_iso":"37.a","p":5,"prec":20,"val":1,"unit":17009699681282}}"#)
  let cases := [
    (`WrongPadicClass, badLabel, "WrongPadicClass.stored_padic_label_eq"),
    (`WrongPadicUnit, badUnit, "WrongPadicUnit.stored_padic_arithmetic"),
    (`DuplicatePadic, duplicate, "Supply exactly one complete stored p-adic regulator row")]
  for (name, command, expected) in cases do
    let saved := (← get).messages
    let diagnostics ← try
      elabCommand command
      (← get).messages.toList.mapM fun message => message.data.toString
    catch error => pure [← error.toMessageData.toString]
    let env ← getEnv
    set { (← get) with messages := saved }
    unless diagnostics.any (fun diagnostic => (diagnostic.splitOn expected).length > 1) do
      throwError "Expected stored regulator rejection at {expected}"
    for suffix in [`curve, `witness, `stored_padic_evidence, `stored_padic_regulator_fact,
        `certificate] do
      if env.contains (name ++ suffix) then
        throwError "A rejected stored regulator leaked {name ++ suffix}"

end

certify_ec NativePadicWithoutEvidence from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"lmfdb_iso":"37.a","p":5,"prec":20,"val":1,"unit":17009699681281}"#

example : NativePadicWithoutEvidence.certificate.analytic.storedPadicRegulator.isNone = true := rfl

run_cmd do
  let modularity := ``VerifiedLcalc.Assumptions.ellipticModularity
  unless (← liftTermElabM <| Lean.collectAxioms ``Checked.conductor).contains modularity do
    throwError "Expected the mixed certificate's conductor to depend on modularity"
  for declaration in [``Checked.certificate, ``importedStoredPadicCoordinates,
      ``importedStoredPadicValuation] do
    for axiomName in ← liftTermElabM <| Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected stored regulator axiom in {declaration}: {axiomName}"
