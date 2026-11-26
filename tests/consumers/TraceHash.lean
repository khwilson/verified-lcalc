/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.TraceHash
import VerifiedLcalc.EllipticCurve.SparsePointCount

/-! # Imported trace-hash evidence and full-vector dispatch -/

open VerifiedLcalc EllipticCurve VerifiedLcalcTests.TraceHash37 Lean Elab Command

example : lmfdbTraceHashWeights.length = 464 := by decide +kernel
example : coefficients.length = 464 := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 2000000 in
-- The independent coefficient check evaluates all 4099 finite-field fibers in the kernel.
/-- Independently verify the first coefficient with the existing local-minimality evaluator. -/
theorem first_trace_coefficient :
    (curve.baseChange ℚ).LFunction 4099 = -58 := by
  let w : EllipticWitness := { equation := curve, primeCoefficients := some [(4099, -58)] }
  exact w.primeCoefficientsValid_sound (by decide +kernel) (by decide +kernel) _ _ (by decide)

local instance : Fact (Nat.Prime 4099) := ⟨by norm_num⟩

set_option maxRecDepth 20000 in
example : pointOrderTraceCheck curve 4099 0 1 (-58) = false := by decide +kernel

set_option maxRecDepth 20000 in
example : pointOrderTraceCheck curve 4099 0 0 (-57) = false := by decide +kernel

/-- The compiled certificate supplies the exact mathematical fingerprint equality. -/
theorem imported_trace_hash :
    lmfdbTraceHash (Checked.curve.baseChange ℚ) = 1127515239490717889 :=
  (Checked.certificate.traceHash.get (by rfl)).correct

example : (Checked.certificate.traceHash.get (by rfl)).evidence.coefficients = coefficients :=
  rfl

certify_ec TypedHash from
  { equation := curve, traceHash := some 1127515239490717889 }
  with_proofs proofs

example : TypedHash.certificate.traceHash.isSome = true := rfl

run_cmd do
  let saved := (← get).messages
  let diagnostics ← try
    elabCommand (← `(certify_ec WrongTraceHash from
      { equation := curve, traceHash := some 1127515239490717890 } with_proofs proofs))
    (← get).messages.toList.mapM fun message => message.data.toString
  catch error => pure [← error.toMessageData.toString]
  let env ← getEnv
  set { (← get) with messages := saved }
  let expected := "failed checking WrongTraceHash.trace_hash_value_valid"
  unless diagnostics.any (fun diagnostic => (diagnostic.splitOn expected).length > 1) do
    throwError "Expected exact trace-hash comparison to reject the wrong value"
  for suffix in [`curve, `witness, `trace_hash_coefficients, `trace_hash_fact, `certificate] do
    if env.contains (`WrongTraceHash ++ suffix) then
      throwError "A rejected trace-hash comparison leaked {suffix}"

certify_ec MissingVector from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"trace_hash":"1127515239490717889","ap":[[2,-2]]}"#

example : MissingVector.certificate.traceHash.isNone = true := rfl

run_cmd do
  let modularity := ``VerifiedLcalc.Assumptions.ellipticModularity
  unless (← liftTermElabM <| Lean.collectAxioms ``Checked.conductor).contains modularity do
    throwError "Expected the mixed certificate's conductor to depend on modularity"
  for declaration in [``Checked.certificate, ``imported_trace_hash, ``first_trace_coefficient,
      ``coefficients_correct] do
    for axiomName in ← liftTermElabM <| Lean.collectAxioms declaration do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected trace-hash axiom in {declaration}: {axiomName}"
