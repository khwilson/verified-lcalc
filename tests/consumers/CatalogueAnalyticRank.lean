import CertifiedCurves.Json
import Lean

/-! # Check native ranks against independently certified curve orders -/

open Lean Elab Command VerifiedLcalc Modularity

example (m : ArithmeticModularRealization Curve11.curve) :
    analyticOrderAt m.formL 1 = 0 :=
  Curve11.catalogue_rank.correct m

example (m : ArithmeticModularRealization Curve37.curve) :
    analyticOrderAt m.formL 1 = 1 :=
  Curve37.catalogue_analytic_rank m

example :
    Curve11.catalogue_rank =
      Curve11.certificate.analytic.rank.get Curve11.catalogue_rank_available :=
  rfl

namespace ImportedRank

def curve := Curve37.curve

instance : (curve.baseChange ℚ).IsElliptic :=
  inferInstanceAs ((Curve37.curve.baseChange ℚ).IsElliptic)

def witness : EllipticWitness := { equation := curve, catalogueAnalyticRank := some 1 }

def certificate : EllipticCertificate curve := Curve37.certificate

end ImportedRank

-- A reused typed certificate can have a rank without a newly emitted analytic_rank declaration.
run_cmd CertifyEC.certifyCatalogueRank `ImportedRank

example (m : ArithmeticModularRealization ImportedRank.curve) :
    analyticOrderAt m.formL 1 = 1 :=
  ImportedRank.catalogue_analytic_rank m

certify_ec RankWithNoPayload from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"rank":4,"analytic_rank":2}"#

certify_ec RankWithNoArithmetic from
  { Curve37.witness with minimality := none, localData := none }

example : RankWithNoPayload.witness.algebraicRank = some 4 := rfl
example : RankWithNoPayload.witness.catalogueAnalyticRank = some 2 := rfl
example : RankWithNoPayload.certificate.analytic.rank.isNone = true := rfl
example : RankWithNoArithmetic.certificate.analytic.rank.isNone = true := rfl

run_cmd do
  for base in [`RankWithNoPayload, `RankWithNoArithmetic] do
    if (← getEnv).contains (base ++ `catalogue_rank) then
      throwError "Unverified native rank became a theorem: {base}"
  let saved := (← get).messages
  let mut failed := false
  try
    elabCommand (← `(certify_ec WrongCatalogueRank from
      { Curve37.witness with catalogueAnalyticRank := some 0 }))
    failed := (← get).messages.hasErrors
  catch _ => failed := true
  let env ← getEnv
  set { (← get) with messages := saved }
  unless failed do throwError "Mismatched native rank was accepted"
  for suffix in [`curve, `witness, `analytic_rank, `catalogue_rank, `catalogue_analytic_rank] do
    if env.contains (`WrongCatalogueRank ++ suffix) then
      throwError "Rejected native rank leaked {suffix}"
  for name in [``Curve11.catalogue_rank, ``Curve37.catalogue_analytic_rank] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected catalogue-rank axiom: {axiomName}"
