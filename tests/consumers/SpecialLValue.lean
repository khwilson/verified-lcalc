import CertifiedCurves.Json
import Lean

/-! # Check LMFDB Taylor leading coefficients -/

open Lean Elab Command VerifiedLcalc Modularity

example : (Curve11.certificate.analytic.specialValue.get (by decide +kernel)).order = 0 :=
  by decide

example : (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order = 1 :=
  by decide

/-- The 11.a1 report is checked against the actual central-value enclosure. -/
theorem imported_11a1_special_value
    (m : ArithmeticModularRealization Curve11.curve) :
    analyticOrderAt m.formL 1 =
        (Curve11.certificate.analytic.specialValue.get (by decide +kernel)).order ∧
      |(iteratedDeriv
          (Curve11.certificate.analytic.specialValue.get (by decide +kernel)).order
          m.formL 1).re /
          (Nat.factorial
            (Curve11.certificate.analytic.specialValue.get (by decide +kernel)).order : ℝ) -
        (((Curve11.certificate.analytic.specialValue.get (by decide +kernel)).claim.reported :
          Rat) : ℝ)| ≤
            (((Curve11.certificate.analytic.specialValue.get (by decide +kernel)).claim.error :
              Rat) : ℝ) :=
  (Curve11.certificate.analytic.specialValue.get (by decide +kernel)).correct m

/-- The 37.a1 Sage real literal is checked against the normalized first derivative. -/
theorem imported_37a1_special_value
    (m : ArithmeticModularRealization Curve37.curve) :
    analyticOrderAt m.formL 1 =
        (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order ∧
      |(iteratedDeriv
          (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order
          m.formL 1).re /
          (Nat.factorial
            (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order : ℝ) -
        (((Curve37.certificate.analytic.specialValue.get (by decide +kernel)).claim.reported :
          Rat) : ℝ)| ≤
            (((Curve37.certificate.analytic.specialValue.get (by decide +kernel)).claim.error :
              Rat) : ℝ) :=
  (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).correct m

/-- The typed analytic aggregate exposes the same proof as the generated facts. -/
theorem imported_37a1_aggregate_projection
    (m : ArithmeticModularRealization Curve37.curve) :
    analyticOrderAt m.formL 1 =
        (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order ∧
      |(iteratedDeriv
          (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order
          m.formL 1).re /
          (Nat.factorial
            (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).order : ℝ) -
        (((Curve37.certificate.analytic.specialValue.get
          (by decide +kernel)).claim.reported : Rat) : ℝ)| ≤
            (((Curve37.certificate.analytic.specialValue.get
              (by decide +kernel)).claim.error : Rat) : ℝ) :=
  (Curve37.certificate.analytic.specialValue.get (by decide +kernel)).correct m

certify_ec PrecisionOnlySpecialValue from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"special_value":{"__RealLiteral__":0,
    "data":"0.30599977383405230182048368332169132525","prec":127}}"#

example : PrecisionOnlySpecialValue.witness.specialLValue = none := rfl
example : PrecisionOnlySpecialValue.certificate.analytic.specialValue = none := rfl

certify_ec NoNumericSpecial from
  { Curve37.witness with centralResult := none, derivativeResult := none }

example : NoNumericSpecial.certificate.analytic.specialValue = none := rfl

certify_ec MissingArithmeticSpecial from
  { Curve37.witness with minimality := none, localData := none }

example : MissingArithmeticSpecial.certificate.analytic.specialValue = none := rfl

private meta def expectRejectedSpecialValue (name : Name) (command : Syntax) :
    CommandElabM Unit := do
  let messages := (← get).messages
  let mut rejected := false
  try
    elabCommand command
    rejected := (← get).messages.hasErrors
  catch _ => rejected := true
  let env ← getEnv
  set { (← get) with messages := messages }
  unless rejected do throwError "Accepted contradictory special value: {name}"
  for suffix in [`curve, `witness, `analytic_rank, `certificate,
      `claimed_special_value, `special_value_input_eq, `special_value_valid,
      `special_value_error_nonnegative] do
    if env.contains (name ++ suffix) then
      throwError "Rejected special value leaked {name ++ suffix}"

run_cmd do
  expectRejectedSpecialValue `BadSpecialValue (← `(certify_ec BadSpecialValue from
    { Curve11.witness with
      specialLValue := some { reported := 2, error := 1 / 100 } }))
  expectRejectedSpecialValue `NegativeSpecialError (← `(certify_ec NegativeSpecialError from
    { Curve11.witness with
      specialLValue := some { reported := 0, error := -1 } }))
  expectRejectedSpecialValue `NegativeErrorWithoutPayload
    (← `(certify_ec NegativeErrorWithoutPayload from
      { equation := Curve11.curve,
        specialLValue := some { reported := 0, error := -1 } }))
  expectRejectedSpecialValue `NegativeJsonSpecialError (← `(certify_ec
    NegativeJsonSpecialError from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"special_value":"1.25",
      "special_value_evidence":{"error":[-1,10]}}"#))
  expectRejectedSpecialValue `MalformedSpecialDecimal (← `(certify_ec
    MalformedSpecialDecimal from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"special_value":"not-a-decimal",
      "special_value_evidence":{"error":[1,10]}}"#))
  for theoremName in [``imported_11a1_special_value, ``imported_37a1_special_value,
      ``imported_37a1_aggregate_projection] do
    let axioms ← liftTermElabM (Lean.collectAxioms theoremName)
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected special-value axiom in {theoremName}: {axiomName}"
