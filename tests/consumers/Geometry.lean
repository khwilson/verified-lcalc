/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.Geometry
import VerifiedLcalc.UpstreamCandidates.TauCeti.ConductorDenominator

/-! Import the normalized twist, geometric-endomorphism, and Szpiro contracts. -/

open VerifiedLcalc VerifiedLcalcTests.Geometry Lean Elab Command

example : Geometry37.certificate.minimumQuadraticTwist = some { minimum := twist37 } := rfl

example : Geometry37.minimum_quadratic_twist_fact.equation =
    Geometry37.claimed_min_quad_twist_ainvs :=
  Geometry37.min_quad_twist_ainvs

example : Geometry37.minimum_quadratic_twist_fact.discriminant = 1 :=
  Geometry37.min_quad_twist_disc

example (d : ℚ) (h : ((Geometry37.curve.baseChange ℚ).quadraticTwistOf 0 (-d)).IsElliptic) :
    letI := h
    37 ≤ Ideal.absNorm (((Geometry37.curve.baseChange ℚ).quadraticTwistOf 0 (-d)).algorithmicConductor
      ℤ) := minimum37 d h

example : Geometry37.certificate.modifiedSzpiroRatio = some Geometry37.szpiro_ratio_fact := rfl

example : |Real.log 110592 / Real.log 37 - (3.216246758769211 : ℝ)| ≤ (0.00000000000001 : ℝ) := by
  let fact := Geometry37.certificate.modifiedSzpiroRatio.get (by rfl)
  have h := fact.within_error
  have hnum : max (Geometry37.curve.c₄.natAbs ^ 3) (Geometry37.curve.c₆.natAbs ^ 2) =
      110592 := by decide +kernel
  have hconductor : fact.conductor = 37 := by decide +kernel
  have hreported : fact.reported = 3.216246758769211 := by decide +kernel
  have herror : fact.error = 0.00000000000001 := by decide +kernel
  rw [hnum, hconductor, hreported, herror] at h
  norm_num at h ⊢
  exact h

certify_ec Reports from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"cm":0,"min_quad_twist_ainvs":[0,0,1,-1,0],
      "min_quad_twist_disc":1,"szpiro_ratio":"3.216246758769211"}"#

example : Reports.certificate.complexMultiplication = none := rfl
example : Reports.certificate.minimumQuadraticTwist = none := rfl
example : Reports.certificate.modifiedSzpiroRatio = none := rfl

private meta def rejectGeometry (base : Name) (command : Syntax) (expected : String) :
    CommandElabM Unit := do
  let messages := (← get).messages
  let message ← try
    elabCommand command
    pure ((← get).messages.toList.getLast?.map (·.data))
  catch error =>
    pure (some error.toMessageData)
  let env ← getEnv
  set { (← get) with messages }
  let result ← (message.getD "").toString
  unless (result.splitOn expected).length > 1 do
    throwError "Expected rejection of {base} with '{expected}', got {result}"
  for suffix in [`curve, `witness, `integral_proofs, `cm_fact, `minimum_quadratic_twist_fact,
      `minimum_quadratic_twist_evidence, `szpiro_ratio_fact, `szpiro_ratio_valid, `certificate] do
    if env.contains (base ++ suffix) then throwError "Rejected geometry leaked {base ++ suffix}"

run_cmd do
  let env ← getEnv
  for suffix in [`cm, `min_quad_twist_ainvs, `min_quad_twist_disc, `szpiro_ratio_fact] do
    if env.contains (`Reports ++ suffix) then throwError "Unchecked report gained a theorem"
  rejectGeometry `WrongTwistEquation (← `(certify_ec WrongTwistEquation from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"min_quad_twist_ainvs":[0,0,1,-2,0]}"#
    with_proofs arithmeticProofs)) "failed checking WrongTwistEquation.min_quad_twist_ainvs"
  rejectGeometry `WrongTwistDisc (← `(certify_ec WrongTwistDisc from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"min_quad_twist_disc":-4}"#
    with_proofs arithmeticProofs)) "failed checking WrongTwistDisc.min_quad_twist_disc"
  rejectGeometry `WrongRatio (← `(certify_ec WrongRatio from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"szpiro_ratio":"1.0","szpiro_ratio_evidence":{"error":"0.01"}}"#
    with_proofs arithmeticProofs)) "failed checking WrongRatio.szpiro_ratio_valid"
  rejectGeometry `MalformedTwist (← `(certify_ec MalformedTwist from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"min_quad_twist_ainvs":[0,0,0,0]}"#))
    "Expected five Weierstrass coefficients"
  for declaration in [``Geometry37.certificate, ``Geometry37.min_quad_twist_ainvs,
      ``Geometry37.min_quad_twist_disc, ``Geometry37.szpiro_ratio_fact,
      ``Geometry37WithCM.certificate, ``Geometry37WithCM.cm, ``minimum37,
      ``WeierstrassCurve.prime_dvd_absNorm_algorithmicConductor_of_dvd_j_den] do
    for assumption in ← liftTermElabM (Lean.collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected axiom {assumption} in {declaration}"

section

variable {W : WeierstrassCurve ℚ} [W.IsElliptic] [h : GeometryHypotheses W]

example (other : MinimumQuadraticTwistFacts Geometry37WithCM.curve) :
    let := other.elliptic
    WeierstrassCurve.IsReducedMinimal (other.equation.baseChange ℚ) →
      other.equation = Geometry37WithCM.claimed_min_quad_twist_ainvs ∧
        other.discriminant = Geometry37WithCM.claimed_min_quad_twist_disc := by
  intro _ reduced
  let evidence := Geometry37WithCM.certificate.minimumQuadraticTwist.get (by rfl)
  have hUnique := (evidence.uniqueMinimum.get (by rfl)).unique other reduced
  exact ⟨hUnique.1.trans Geometry37WithCM.min_quad_twist_ainvs,
    hUnique.2.trans Geometry37WithCM.min_quad_twist_disc⟩

example : Nonempty (ℤ ≃+* (Geometry37WithCM.curve.baseChange ℚ).GeometricEnd) := by
  let cm := Geometry37WithCM.certificate.complexMultiplication.get (by rfl)
  rcases cm.endomorphismRing with h | h
  · exact h.2
  · exact (lt_irrefl (0 : ℤ) h.1).elim

run_cmd do
  rejectGeometry `WrongCM (← `(certify_ec WrongCM from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"cm":-4}"#
    with_proofs (nonCMProofs h.ofEquation))) "failed checking WrongCM.cm"

end
