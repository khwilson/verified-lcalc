/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.BSDPeriod
import VerifiedLcalcTests.Fixtures.BSDSha
import VerifiedLcalc.Certificate.Analytic.BSDQuotient

/-! # Check imported period, Tamagawa, and analytic quotient evidence -/

open Lean Elab Command VerifiedLcalc

theorem imported_minimal_real_period_enclosure :
    let p := Curve17a2.PeriodCertificate.certificate.realPeriod.get (by decide +kernel)
    |(Curve17a2.PeriodCertificate.curve.baseChange ℚ).minimalRealPeriod -
      (p.reported : ℝ)| ≤ (p.error.val : ℝ) :=
  (Curve17a2.PeriodCertificate.certificate.realPeriod.get (by decide +kernel)).correct

theorem imported_intrinsic_tamagawa_product :
    (Curve37a1Tamagawa.TamagawaCertificate.curve.baseChange ℚ).tamagawaProduct (R := ℤ) = 1 :=
  (Curve37a1Tamagawa.TamagawaCertificate.certificate.tamagawaProduct.get
    (by decide +kernel)).correct

section Sha

open Curve37a1Sha

variable {order : ℕ} [h : GivenQuotientEvidence order]

example : (ShaCertificate.certificate.analyticSha.get (by rfl)).reported = 1 := rfl
example : (ShaCertificate.certificate.analyticSha.get (by rfl)).error.val = 1 / 100 :=
  rfl

include h in
/-- The actual quotient of this explicit realization rounds to the checked integer. -/
theorem imported_sha_integer (m : Modularity.ArithmeticModularRealization ShaCertificate.curve) :
    let E := ShaCertificate.curve.baseChange ℚ
    round ((iteratedDeriv 1 m.formL 1).re / ((Nat.factorial 1 : ℕ) : ℝ) *
      (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
      (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ))) = 1 :=
  (ShaCertificate.certificate.roundedAnalyticSha.get (by rfl)).round_eq m

/-- The exact prime divisors of the proved rounded integer. -/
theorem imported_sha_prime_support :
    let fact := ShaCertificate.certificate.roundedAnalyticSha.get (by rfl)
    (fact.primes.get (by rfl)).val = fact.value.primeFactors :=
  ((ShaCertificate.certificate.roundedAnalyticSha.get (by rfl)).primes.get
    (by rfl)).property

end Sha

-- Check the exact JSON decoder and the absence of mathematical evidence.
certify_ec BSDReportsOnly from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"real_period":2.99,"tamagawa_product":1,
      "sha_an":"8.999","sha_an_evidence":{"error":[1,100]},"sha":9,"sha_primes":[3]}"#

example : BSDReportsOnly.supplied.analyticSha = some ⟨8999 / 1000, some (1 / 100)⟩ := by
  decide +kernel
example : BSDReportsOnly.certificate.realPeriod.isNone = true := rfl
example : BSDReportsOnly.certificate.tamagawaProduct.isNone = true := rfl
example : BSDReportsOnly.certificate.analyticSha.isNone = true := rfl
example : BSDReportsOnly.certificate.roundedAnalyticSha.isNone = true := rfl

private meta def expectRejected (name : Name) (command : Syntax)
    (label : Option String := none) : CommandElabM Unit := do
  let messages := (← get).messages
  let failed ← try
    elabCommand command
    pure (← get).messages.hasErrors
  catch error =>
    if let some label := label then
      let message ← error.toMessageData.toString
      unless (message.splitOn s!"failed checking {name}.{label}").length > 1 do
        throwError "Expected check {name}.{label} to reject the input, got {message}"
    pure true
  set { (← get) with messages }
  unless failed do throwError "Invalid BSD report accepted: {name}"
  for suffix in [`curve, `integral_proofs, `certificate, `reported_sha,
      `real_period_fact, `tamagawa_product_fact, `analytic_sha_fact, `rounded_analytic_sha_fact] do
    if (← getEnv).contains (name ++ suffix) then
      throwError "Rejected BSD report leaked {name ++ suffix}"

run_cmd do
  expectRejected `WrongPeriod (← `(certify_ec WrongPeriod from
    { equation := Curve17a2.model, realPeriod := some ⟨3, none⟩ }
    with_proofs { realPeriod := some Curve17a2.period }))
  expectRejected `WrongTamagawa (← `(certify_ec WrongTamagawa from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"tamagawa_product":2}"#
    with_proofs { tamagawaProduct := some Curve37a1Tamagawa.product }))
  expectRejected `UnprovedRadius (← `(certify_ec UnprovedRadius from_json_string
    r#"{"ainvs":[1,-1,1,-6,-4],"real_period":"3.0941595071022403464191580099",
        "real_period_evidence":{"error":"1/100"}}"#
    with_proofs { realPeriod := some Curve17a2.period }))
  expectRejected `ShaTie (← `(certify_ec ShaTie from
    { equation := Curve37a1Tamagawa.model, analyticSha := some ⟨9, some (1 / 2)⟩,
      sha := some 9 }))
  expectRejected `ShaRepeatedPrime (← `(certify_ec ShaRepeatedPrime from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"sha":9,"sha_primes":[3,3]}"#))
  expectRejected `ShaWrongPrime (← `(certify_ec ShaWrongPrime from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"sha":9,"sha_primes":[2]}"#))

section ShaMismatch

open Curve37a1Sha

variable {order : ℕ} [h : GivenQuotientEvidence order]

run_cmd do
  expectRejected `WrongShaCenter (← `(certify_ec WrongShaCenter from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"sha_an":"2","sha":2}"#
    with_proofs (proofAttachment h.atOne))) (some "sha_an_report_matches")
  expectRejected `WrongShaOrder (← `(certify_ec WrongShaOrder from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"analytic_rank":2,"sha_an":"1","sha":1}"#
    with_proofs (proofAttachment h.atOne))) (some "sha_an_order_matches")
  expectRejected `WrongShaRounded (← `(certify_ec WrongShaRounded from_json_string
    r#"{"ainvs":[0,0,1,-1,0],"sha_an":"1","sha_an_evidence":{"error":"1/100"},"sha":2}"#
    with_proofs (proofAttachment h.atOne))) (some "sha_report_consistent")

end ShaMismatch

section Quotient
variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]

theorem conditional_quotient_enclosure (leading : SpecialLValueFacts curve)
    (torsion : { n : ℕ //
      Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n })
    (period : RealPeriodFact curve) (regulator : RegulatorFacts (curve.baseChange ℚ))
    (tamagawa : TamagawaProductFact curve) (report : ℚ) (error : { r : ℚ // 0 ≤ r })
    (positive : 0 < (AnalyticShaFact.denominatorBounds period regulator tamagawa).1)
    (lower : report - error.val ≤
      (AnalyticShaFact.quotientBounds leading torsion period regulator tamagawa).1)
    (upper : (AnalyticShaFact.quotientBounds leading torsion period regulator tamagawa).2 ≤
      report + error.val) (m : Modularity.ArithmeticModularRealization curve) :
    let E := curve.baseChange ℚ
    |(iteratedDeriv leading.order m.formL 1).re / (leading.order.factorial : ℝ) *
      (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
      (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ)) -
      (report : ℝ)| ≤ (error.val : ℝ) :=
  (AnalyticShaFact.ofFactors leading torsion period regulator tamagawa report error
    positive lower upper).correct m

theorem conditional_rounded_analytic_quotient (fact : RoundedAnalyticShaFact curve)
    (m : Modularity.ArithmeticModularRealization curve) :
    let E := curve.baseChange ℚ
    round ((iteratedDeriv fact.analytic.order m.formL 1).re /
      (fact.analytic.order.factorial : ℝ) *
      (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
      (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ))) =
      (fact.value : ℤ) :=
  fact.round_eq m

end Quotient

run_cmd do
  for name in [``imported_minimal_real_period_enclosure,
      ``imported_intrinsic_tamagawa_product,
      ``Curve37a1Sha.ShaCertificate.certificate, ``imported_sha_integer,
      ``imported_sha_prime_support,
      ``conditional_quotient_enclosure,
      ``conditional_rounded_analytic_quotient] do
    for ax in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
