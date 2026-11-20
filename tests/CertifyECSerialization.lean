import VerifiedLcalc.Tactic.CertifyEC
import Lean

open Lean Elab Command Meta VerifiedLcalc VerifiedLcalc.EllipticCurve

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

-- Certificate serialization must ignore user-interface display limits.
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 1
set_option pp.maxSteps 1

run_cmd do
  let e : WeierstrassCurve ℤ := ⟨0, 0, 1, -7, 12⟩
  let some r := evaluateDerivative e 245 64 2 16
    | throwError "Could not construct the 245.a1 regression input"
  let some m := minimalityWitness? e [5, 7]
    | throwError "Could not construct minimality evidence"
  let some d := wildData? e
    | throwError "Could not construct local reduction evidence"
  -- A data round-trip at the JSON profile's maximum coefficient count.
  let long : EllipticWitness := .derivative
    { r with termLimit := 128, coefficients := List.replicate 128 (-1) } m d
  let original := toExpr long
  let stx ← CertifyEC.literalSyntax original
  liftTermElabM do
    let restored ← Term.elabTerm stx (some (mkConst ``EllipticWitness))
    unless ← isDefEq original restored do
      throwError "Serialization changed the supplied witness"
  -- Explicit test-side production; certify_ec itself still verifies only.
  let input ← CertifyEC.literalSyntax (toExpr (EllipticWitness.derivative r m d))
  let name := mkIdent `Serialization245
  elabCommand (← `(certify_ec $name:ident from $input))

-- The resulting theorem is ordinary mathematical evidence in the caller's file.
example : analyticOrderAt
    (VerifiedLcalc.Modularity.modularWitness Serialization245.curve
      Serialization245.nonsingular).formL (1 : ℂ) = 1 :=
  Serialization245.analytic_rank

run_cmd do
  let axioms ← liftTermElabM <| Lean.collectAxioms `Serialization245.payload_correct
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "Unexpected axiom in serialization regression: {axiomName}"
