import CertifiedCurves

/-! # Imported analytic and arithmetic certificate theorems

These checks use the compiled certificates for the three JSON fixtures.
-/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.Modularity

/-- The completed rank-one certificate is usable from another Lean module. -/
theorem curve37_rank :
    analyticOrderAt (modularWitness Curve37.curve Curve37.nonsingular).formL (1 : ℂ) = 1 :=
  Curve37.analytic_rank

example : analyticOrderAt (modularWitness Curve11.curve Curve11.nonsingular).formL (1 : ℂ) =
    0 :=
  Curve11.analytic_rank

example : analyticOrderAt (modularWitness Curve112.curve Curve112.nonsingular).formL (1 : ℂ) =
    1 :=
  Curve112.analytic_rank

example : Curve37.certifiedRank.val = 1 := rfl

/-- The named coefficient theorem identifies the twelve stored values. -/
theorem curve37_coefficients :
    (List.range 12).map (fun n => (Curve37.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, -2, -3, 2, -2, 6, -1, 0, 6, 4, -5, -6] :=
  Curve37.l_function_coefficients

/-- The aggregate carries the same checked coefficient prefix. -/
theorem curve37_certificate_coefficients :
    (List.range 12).map (fun n => (Curve37.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, -2, -3, 2, -2, 6, -1, 0, 6, 4, -5, -6] :=
  (Curve37.certificate.arithmetic.dirichletCoefficients.get (by rfl)).property

example : (List.range 1).map (fun n => (Curve11.curve.baseChange ℚ).LFunction (n + 1)) =
    [1] :=
  Curve11.l_function_coefficients

run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let rankAxioms ← liftTermElabM (Lean.collectAxioms ``curve37_rank)
  let rankProjectAxioms := rankAxioms.toList.filter fun name => !(allowed.contains name)
  unless rankProjectAxioms == [``Assumptions.ellipticModularity] do
    throwError "Unexpected project axioms in curve37_rank: {rankProjectAxioms}"
  for proof in [``curve37_coefficients, ``curve37_certificate_coefficients,
      ``Curve11.l_function_coefficients] do
    for name in ← liftTermElabM (Lean.collectAxioms proof) do
      unless allowed.contains name do
        throwError "Unexpected axiom in {proof}: {name}"
