/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.CremonaLabels
import VerifiedLcalc.Verification.LmfdbCatalogue

/-! # Exact imported Cremona singleton facts and separate prerequisites -/

open VerifiedLcalc EllipticCurve VerifiedLcalcTests.Cremona43
open Lean Elab Command
open VerifiedLcalcTests.LmfdbCatalogue43 (source model roster CurveComplete RosterComplete)

section

variable {E R : WeierstrassCurve ℚ} [hE : CurveComplete E] [hR : RosterComplete R]

example : (Checked.certificate.cremonaCatalogue.get (by rfl)).isoLabel.map Subtype.val =
    some "43a" := rfl
example : (Checked.certificate.cremonaCatalogue.get (by rfl)).curveLabel.map Subtype.val =
    some "43a1" := rfl
example : (Checked.certificate.cremonaCatalogue.get (by rfl)).number.map Subtype.val =
    some 1 := rfl

include hE hR in
/-- The exact label proof can be recovered with the same indexed conductor scope. -/
theorem imported_cremona_label : cremonaSingletonCurveLabel 43 = "43a1" :=
  ((Checked.certificate.cremonaCatalogue.get (by rfl)).curveLabel.get (by rfl)).property.2.2

/-- The selected conductor-roster class has index zero independently of its ordering. -/
theorem imported_cremona_class_index :
    let fact := Checked.certificate.cremonaCatalogue.get (by rfl)
    (fact.evidence.onlyClass.get (by rfl)).val.classIndex.val = 0 :=
  (Checked.certificate.cremonaCatalogue.get (by rfl)).evidence.classIndex_zero (by rfl)

/-- The selected within-class position gives historical number one. -/
theorem imported_cremona_curve_index :
    let fact := Checked.certificate.cremonaCatalogue.get (by rfl)
    (fact.evidence.onlyCurve.get (by rfl)).val.curveIndex.val + 1 = 1 :=
  (Checked.certificate.cremonaCatalogue.get (by rfl)).evidence.curveIndex_one (by rfl)

certify_ec OnlyNumber from
  { equation := source, cremonaNumber := some 1, cremonaIso := some "43a" }
  with_proofs ({ cremonaSingleton := some { rangeEvidence with
    onlyCurve := some ⟨model hE, rfl⟩ } } : IntegralCurveProofs source)

example : (OnlyNumber.certificate.cremonaCatalogue.get (by rfl)).number.isSome = true := rfl
example : (OnlyNumber.certificate.cremonaCatalogue.get (by rfl)).isoLabel.isNone = true := rfl

certify_ec OnlyClass from
  { equation := source, cremonaIso := some "43a", cremonaLabel := some "43a1" }
  with_proofs ({ cremonaSingleton := some { rangeEvidence with
    onlyClass := some ⟨roster hR, rfl⟩ } } : IntegralCurveProofs source)

example : (OnlyClass.certificate.cremonaCatalogue.get (by rfl)).isoLabel.isSome = true := rfl
example : (OnlyClass.certificate.cremonaCatalogue.get (by rfl)).curveLabel.isNone = true := rfl

run_cmd do
  let saved := (← get).messages
  let diagnostics ← try
    elabCommand (← `(certify_ec WrongCremonaLabel from
      { equation := source, cremonaLabel := some "43.a1" }
      with_proofs ({ cremonaSingleton := some (evidence hE hR) } : IntegralCurveProofs source)))
    (← get).messages.toList.mapM fun message => message.data.toString
  catch error => pure [← error.toMessageData.toString]
  let env ← getEnv
  set { (← get) with messages := saved }
  let expected := "failed checking WrongCremonaLabel.Clabel"
  unless diagnostics.any (fun diagnostic => (diagnostic.splitOn expected).length > 1) do
    throwError "Expected an incorrect historical label to be rejected at the label comparison"
  for suffix in [`curve, `witness, `cremona_catalogue_fact, `certificate] do
    if env.contains (`WrongCremonaLabel ++ suffix) then
      throwError "A rejected Cremona claim leaked {suffix}"

end

example (candidate : CremonaSingletonEvidence source) : candidate.conductor.val ≠ 500001 := by
  have bound := candidate.conductor.property.2
  omega

certify_ec BareMetadata from_json_string
  r#"{"ainvs":[0,1,1,0,0],"Ciso":"43a","Clabel":"43a1","Cnumber":1}"#

example : BareMetadata.certificate.cremonaCatalogue.isNone = true := rfl

run_cmd do
  let modularity := ``VerifiedLcalc.Assumptions.ellipticModularity
  unless (← liftTermElabM <| Lean.collectAxioms ``Checked.conductor).contains modularity do
    throwError "The mixed certificate should retain its modularity-dependent conductor theorem"
  for declaration in [``Checked.certificate, ``imported_cremona_label,
      ``imported_cremona_class_index, ``imported_cremona_curve_index,
      ``cremonaSingletonClassLabel_eq, ``cremonaSingletonCurveLabel_eq] do
    for axiomName in ← liftTermElabM <| Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected Cremona axiom in {declaration}: {axiomName}"
