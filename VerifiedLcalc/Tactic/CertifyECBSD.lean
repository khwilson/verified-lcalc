/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Certificate.Analytic.BSDQuotient

/-! Check raw period and BSD quotient reports against proofs for the same equation. -/

public meta section

namespace VerifiedLcalc.CertifyEC
open Lean Elab Command Meta

private def attachedFact (attachment : Option Ident) (field : Name) :
    CommandElabM (Option (TSyntax `term)) := do
  let some attachment := attachment | return none
  let projection := mkIdent field
  let selected ← `(($attachment).$projection)
  if ← hasOptionalProof selected field then
    some <$> `(($selected).get (by rfl))
  else pure none

private def validateEnclosureRadius (base label : Name)
    (report : Option (TSyntax `term)) : CommandElabM Unit := do
  if let some raw := report then
    checked (base ++ label)
      (← `(0 ≤ ($raw : DecimalEnclosureClaim).error.getD 0))
      (← `(by decide +kernel))

private def checkEnclosureReport (base : Name) (label : Name)
    (report : Option (TSyntax `term)) (fact : TSyntax `term) : CommandElabM Unit := do
  if let some raw := report then
    checked (base ++ label)
      (← `(let report : DecimalEnclosureClaim := $raw
        report.reported = ($fact).reported ∧
          report.error.getD ($fact).error.val = ($fact).error.val))
      (← `(by constructor <;> first | rfl | decide +kernel))

private def certifyRealPeriod (base : Name) (curve : Ident)
    (attachment : Option Ident) : CommandElabM Unit := do
  let report ← optionalInput (base ++ `witness) `realPeriod
  validateEnclosureRadius base `real_period_error_nonnegative report
  let some fact ← attachedFact attachment `realPeriod |
    if report.isSome then
      logInfo m!"Unverified {base} real period: supply a proved enclosure"
    return
  checkEnclosureReport base `real_period_report_matches report fact
  let name := rootIdent (base ++ `real_period_fact)
  emit (← `(def $name : RealPeriodFact $curve := $fact))

private def certifyTamagawaProduct (base : Name) (curve : Ident)
    (attachment : Option Ident) : CommandElabM Unit := do
  let report ← optionalInput (base ++ `witness) `tamagawaProduct
  let some fact ← attachedFact attachment `tamagawaProduct |
    if report.isSome then
      logInfo m!"Unverified {base} Tamagawa product: supply a proved product"
    return
  if let some value := report then
    checked (base ++ `tamagawa_product_report_matches)
      (← `((($fact).value : Nat) = $value)) (← `(by first | rfl | decide +kernel))
  let name := rootIdent (base ++ `tamagawa_product_fact)
  emit (← `(def $name : TamagawaProductFact $curve := $fact))

private def validateShaReports (base : Name)
    (report value primes : Option (TSyntax `term)) :
    CommandElabM (Option (Ident × TSyntax `term)) := do
  let support ← if let some ps := primes then do
    let supplied := rootIdent (base ++ `reported_sha_primes)
    emit (← `(def $supplied : List Nat := $ps))
    checked (base ++ `sha_primes_distinct) (← `(($supplied).Nodup)) (← `(by decide +kernel))
    pure (some supplied)
  else pure none
  let some value := value | return none
  let n := rootIdent (base ++ `reported_sha)
  emit (← `(def $n : Nat := $value))
  checked (base ++ `sha_positive) (← `(0 < $n)) (← `(by decide +kernel))
  if let some raw := report then
    checked (base ++ `sha_report_consistent)
      (← `(let raw : DecimalEnclosureClaim := $raw
        if let some error := raw.error then |raw.reported - ($n : ℚ)| + error < 1 / 2
        else True))
      (← `(by dsimp only; first | decide +kernel | trivial))
  let support ← if let some ps := support then do
    let name := base ++ `sha_prime_report_matches
    checked name (← `(($ps).toFinset = ($n).primeFactors)) (← `(by decide +kernel))
    `(some ⟨($ps).toFinset, $(rootIdent name)⟩)
  else `(none)
  return some (n, support)

private def certifyRoundedSha (base : Name) (curve : Ident) (analytic : Ident)
    (n : Ident) (support : TSyntax `term) (report : Option (TSyntax `term)) :
    CommandElabM Unit := do
  let rounds := base ++ `sha_rounds
  let proof ← if report.isSome then
    let agreement := rootIdent (base ++ `sha_an_report_matches)
    `(by
      first
      | decide +kernel
      | rw [← ($agreement).1, ← ($agreement).2]
        simp only [Option.getD_some]
        decide +kernel)
  else `(by decide +kernel)
  checked rounds
    (← `(|($analytic).reported - ($n : ℚ)| + ($analytic).error.val < 1 / 2))
    proof
  let rounded := rootIdent (base ++ `rounded_analytic_sha_fact)
  emit (← `(def $rounded : RoundedAnalyticShaFact $curve :=
    ⟨$analytic, $n, $(rootIdent (base ++ `sha_positive)), $(rootIdent rounds), $support⟩))

private def certifyAnalyticSha (base : Name) (curve : Ident)
    (attachment : Option Ident) : CommandElabM Unit := do
  let w := base ++ `witness
  let report ← optionalInput w `analyticSha
  validateEnclosureRadius base `sha_an_error_nonnegative report
  let value ← optionalInput w `sha
  let primes ← optionalInput w `shaPrimes
  let rounded ← validateShaReports base report value primes
  let some fact ← attachedFact attachment `analyticSha |
    if report.isSome || value.isSome || primes.isSome then
      logInfo m!"Unverified {base} analytic BSD quotient: supply a proved enclosure"
    return
  if let some order ← optionalInput w `catalogueAnalyticRank then
    checked (base ++ `sha_an_order_matches)
      (← `((($fact).order : Nat) = $order)) (← `(by first | rfl | decide +kernel))
  let analytic := rootIdent (base ++ `analytic_sha_fact)
  emit (← `(def $analytic : AnalyticShaFact $curve := $fact))
  checkEnclosureReport base `sha_an_report_matches report (← `($analytic))
  if let some (n, support) := rounded then
    certifyRoundedSha base curve analytic n support report
  else if primes.isSome then
    logInfo m!"Unverified {base} sha_primes: supply the rounded quotient sha"

/-- Check all submitted period, Tamagawa product and analytic quotient claims. -/
def certifyBSDFacts (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  let curve := rootIdent (base ++ `curve)
  certifyRealPeriod base curve attachment
  certifyTamagawaProduct base curve attachment
  certifyAnalyticSha base curve attachment

end VerifiedLcalc.CertifyEC
