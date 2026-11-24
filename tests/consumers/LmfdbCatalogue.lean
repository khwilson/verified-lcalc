/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.LmfdbCatalogue

/-! # Imported catalogue label contracts and command regressions -/

open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalcTests.LmfdbCatalogue43
open Lean Elab Command

example : lmfdbClassCode 0 = "a" := by decide +kernel
example : lmfdbClassCode 25 = "z" := by decide +kernel
example : lmfdbClassCode 26 = "ba" := by decide +kernel
example : lmfdbClassCodeValue "ba" = 26 := by decide +kernel

section

variable {E R : WeierstrassCurve ℚ} [hE : CurveComplete E] [hR : RosterComplete R]

example : Checked.certificate.lmfdbCatalogue.number.map Subtype.val = some 1 := rfl
example : Checked.certificate.lmfdbCatalogue.classIndex.map Subtype.val = some 0 := rfl
example : Checked.certificate.lmfdbCatalogue.isoLabel.map Subtype.val = some "43.a" := rfl
example : Checked.certificate.lmfdbCatalogue.curveLabel.map Subtype.val = some "43.a1" := rfl

/-- A compiled consumer can recover the precise proof embodied by the class label. -/
theorem imported_lmfdb_iso_label :
    Checked.certificate.lmfdbCatalogue.roster.map
      (fun r => lmfdbIsoLabel r.conductor r.classIndex.val) = some "43.a" :=
  (Checked.certificate.lmfdbCatalogue.isoLabel.get (by rfl)).property

/-- A compiled consumer can recover the proof joining the two mathematical indices. -/
theorem imported_lmfdb_curve_label :
    let facts := Checked.certificate.lmfdbCatalogue
    (facts.roster.bind fun r => facts.orderedClass.map
      (fun c => lmfdbCurveLabel r.conductor r.classIndex.val (c.1.curveIndex.val + 1))) =
        some "43.a1" :=
  (Checked.certificate.lmfdbCatalogue.curveLabel.get (by rfl)).property

certify_ec OnlyFullLabel from { equation := source, lmfdbLabel := some "43.a1" }
  with_proofs (proofs hE hR)

example : OnlyFullLabel.certificate.lmfdbCatalogue.classIndex.isNone = true := rfl
example : OnlyFullLabel.certificate.lmfdbCatalogue.number.isNone = true := rfl
example : OnlyFullLabel.certificate.lmfdbCatalogue.isoLabel.isNone = true := rfl
example : OnlyFullLabel.certificate.lmfdbCatalogue.curveLabel.map Subtype.val = some "43.a1" :=
  rfl

end

section

variable {E : WeierstrassCurve ℚ} [hE : CurveComplete E]

certify_ec JustCurveOrder from
  { equation := source, lmfdbNumber := some 1, lmfdbIso := some "unverified class" }
  with_proofs ({ isogenyClass := some ⟨model hE, some ordering⟩ } : IntegralCurveProofs source)

example : JustCurveOrder.certificate.lmfdbCatalogue.number.map Subtype.val = some 1 := rfl
example : JustCurveOrder.certificate.lmfdbCatalogue.roster.isNone = true := rfl
example : JustCurveOrder.certificate.lmfdbCatalogue.isoLabel.isNone = true := rfl

certify_ec WithoutReducedOrder from
  { equation := source, lmfdbNumber := some 1 }
  with_proofs ({ isogenyClass := some ⟨model hE, none⟩ } : IntegralCurveProofs source)

example : WithoutReducedOrder.certificate.lmfdbCatalogue.number.isNone = true := rfl

end

section

variable {R : WeierstrassCurve ℚ} [hR : RosterComplete R]

certify_ec JustRoster from
  { equation := source, isoNlabel := some 0, lmfdbIso := some "43.a", lmfdbLabel := some "43.a1" }
  with_proofs ({ conductorClassRoster := some (roster hR) } : IntegralCurveProofs source)

example : JustRoster.certificate.lmfdbCatalogue.classIndex.map Subtype.val = some 0 := rfl
example : JustRoster.certificate.lmfdbCatalogue.isoLabel.map Subtype.val = some "43.a" := rfl
example : JustRoster.certificate.lmfdbCatalogue.curveLabel.isNone = true := rfl
example : JustRoster.certificate.lmfdbCatalogue.orderedClass.isNone = true := rfl

end

certify_ec LabelsAsMetadata from_json_string
  r#"{"ainvs":[0,1,1,0,0],"lmfdb_number":1,"iso_nlabel":0,
      "lmfdb_iso":"43.a","lmfdb_label":"43.a1"}"#

example : LabelsAsMetadata.certificate.lmfdbCatalogue = {} := rfl

/-- Check the intended rejection point and the absence of partially emitted declarations. -/
private meta def expectRejected (base field : Name) (command : Syntax) : CommandElabM Unit := do
  let saved := (← get).messages
  let failure ← try
    elabCommand command
    pure false
  catch error =>
    let message ← error.toMessageData.toString
    pure ((message.splitOn s!"failed checking {base}.{field}").length > 1)
  let env ← getEnv
  set { (← get) with messages := saved }
  unless failure do throwError "Expected rejection while checking {base}.{field}"
  for suffix in [`curve, `witness, `lmfdb_conductor_class_roster, `lmfdb_ordered_class,
      `lmfdb_catalogue, `certificate] do
    if env.contains (base ++ suffix) then
      throwError "Rejected catalogue claim leaked {base ++ suffix}"

section

variable {E R : WeierstrassCurve ℚ} [hE : CurveComplete E] [hR : RosterComplete R]

run_cmd do
  expectRejected `WrongCurveNumber `lmfdb_number (← `(certify_ec WrongCurveNumber from
    { equation := source, lmfdbNumber := some 2 } with_proofs (proofs hE hR)))
  expectRejected `WrongClassIndex `iso_nlabel (← `(certify_ec WrongClassIndex from
    { equation := source, isoNlabel := some 1 } with_proofs (proofs hE hR)))
  expectRejected `WrongClassLabel `lmfdb_iso (← `(certify_ec WrongClassLabel from
    { equation := source, lmfdbIso := some "44.a" } with_proofs (proofs hE hR)))
  expectRejected `WrongCurveLabel `lmfdb_label (← `(certify_ec WrongCurveLabel from_json_string
    r#"{"ainvs":[0,1,1,0,0],"lmfdb_label":"43.a2"}"# with_proofs (proofs hE hR)))

end

run_cmd do
  let modularity := ``VerifiedLcalc.Assumptions.ellipticModularity
  unless (← liftTermElabM <| Lean.collectAxioms ``Checked.conductor).contains modularity do
    throwError "The mixed certificate should retain the modularity-dependent conductor theorem"
  for declaration in [``Checked.certificate, ``imported_lmfdb_iso_label,
      ``imported_lmfdb_curve_label, ``ConductorClassRoster.eq_of_isogeny,
      ``lmfdbClassCodeValue_code] do
    for axiomName in ← liftTermElabM <| Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected catalogue axiom in {declaration}: {axiomName}"
