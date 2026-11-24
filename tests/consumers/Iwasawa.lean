/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.Iwasawa
import Lean

/-! Reuse selected Iwasawa rows and the universal good-prime threshold from compiled proofs. -/

open VerifiedLcalc VerifiedLcalc.Modularity VerifiedLcalcTests.Iwasawa11
open TauCeti.WorkedExamples Lean Elab Command

section

variable {level : ℕ} [h : Interpolation11 level]

private noncomputable def checked11 : IwasawaFacts curve11a2 :=
  Checked11.certificate.iwasawa.get (by rfl)

example : checked11.rows.length = 1 := rfl
example : checked11.rowFor 2 = none := rfl
example : checked11.rowFor 5 = none := rfl
example : (checked11.rowFor 3).isSome = true := rfl
example : (checked11.threshold.get (by rfl)).prime.val = 7 := rfl

example (p : Nat.Primes) (hle : 7 ≤ p.val) (good : iwasawaGood curve11a2 p.val) :
    letI : Fact p.val.Prime := ⟨p.property⟩
    ∃ integral : ℚ → ℤ_[p.val],
      (∀ r, (integral r : ℚ_[p.val]) = (checked11.symbols.value r : ℚ_[p.val])) ∧
      GoodPrimeIwasawaVanishing curve11a2 integral :=
  (checked11.threshold.get (by rfl)).vanishing p hle good

example :
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    ∃ F : PowerSeries ℤ_[3],
      OrdinarilyInterpolates h.symbol3 h.alpha3 F ∧
      F.lambdaInvariant = 0 ∧ F.muInvariant = 0 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let row := (checked11.rowFor 3).get (by rfl)
  let series := row.unsigned.get (by rfl)
  exact ⟨series.series, h.interpolation3, series.order.correct⟩

certify_ec LeanRow from
  ({
    equation := curve11a2
    iwasawaData := some [(3, .inr [0, 0])]
    iwasawaThreshold := some 0 } : EllipticWitness)
  with_proofs (proofs h)

example : (LeanRow.certificate.iwasawa.get (by rfl)).threshold = none := rfl

certify_ec Unknown from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"iwdata":{"3":"o?"},"iwp0":0}"# with_proofs (proofs h)

example : Unknown.certificate.iwasawa = none := rfl

end

certify_ec Bare from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"iwdata":{"3":[0,0]},"iwp0":7}"#

example : Bare.certificate.iwasawa = none := rfl

private meta def rejectClaim (base : Name) (cmd : Syntax) (suffix : Name) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand cmd
    failed := (← get).messages.hasErrors
  catch err =>
    let msg ← err.toMessageData.toString
    unless (msg.splitOn s!"failed checking {base ++ suffix}").length > 1 do
      throwError "Expected {base ++ suffix} to fail, got {msg}"
    failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Bad Iwasawa claim accepted for {base}"
  for decl in [`curve, `witness, `iwasawa_evidence, `iwasawa_fact, `iwp0, suffix, `certificate] do
    if env.contains (base ++ decl) then throwError "Rejected Iwasawa claim leaked {base ++ decl}"

section

variable {level : ℕ} [h : Interpolation11 level]

run_cmd do
  rejectClaim `BadRow (← `(certify_ec BadRow from_json_string
    r#"{"ainvs":[0,-1,1,-10,-20],"iwdata":{"3":[1,0]},"iwp0":7}"#
    with_proofs (proofs h))) `iwdata.entry0.value
  rejectClaim `BadBound (← `(certify_ec BadBound from
    ({ equation := curve11a2, iwasawaThreshold := some 11 } : EllipticWitness)
    with_proofs (proofs h))) `iwp0
  for name in [``IwasawaSeriesOrder.correct, ``IwasawaThresholdEvidence.vanishing,
      ``Checked11.iwp0, ``Checked11.certificate, ``LeanRow.certificate] do
    for ax in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

end
