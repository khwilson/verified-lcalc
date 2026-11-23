/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyECCommon
public import VerifiedLcalc.Certificate.Support.GaloisImage
public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public meta import Lean

/-! # Compare Galois-image reports with exact proof attachments -/

public meta section

namespace VerifiedLcalc.CertifyEC

open Lean Elab Command

private def suppliedProof (base field : Name) : CommandElabM (Option (TSyntax `term)) := do
  let name := base ++ `integral_proofs
  unless (← getEnv).contains name do return none
  let attachment := rootIdent name
  let projection := rootIdent (``IntegralCurveProofs ++ field)
  let selected ← `($projection $attachment)
  if ← hasOptionalProof selected field then
    return some (← `(($selected).get (by rfl)))
  return none

/-- Check the exceptional prime list and radical against complete non-CM local image evidence. -/
def certifyNonmaxPrimes (base : Name) : CommandElabM Unit := do
  let primes ← bindStored base `nonmaxPrimes `nonmax_primes (← `(List ℕ))
  let radical ← bindStored base `nonmaxRadical `nonmax_rad (← `(ℕ))
  if primes.isNone && radical.isNone then return
  if let some ps := primes then
    checked (base ++ `nonmax_primes_shape)
      (← `(($ps).Nodup ∧ ($ps).all (fun p => decide (Nat.Prime p)) = true))
      (← `(by decide +kernel))
  if let some n := radical then
    checked (base ++ `nonmax_rad_positive) (← `(0 < $n)) (← `(by decide +kernel))
  let some proof ← suppliedProof base `nonmaxSupport
    | logInfo m!"Unverified {base} exceptional-prime claims: supply complete non-CM image evidence"
  let curve := rootIdent (base ++ `curve)
  let support := rootIdent (base ++ `nonmax_prime_support)
  emit (← `(def $support : NonmaxPrimeSupportFact $curve := $proof))
  auditAxioms (base ++ `nonmax_prime_support)
  if let some ps := primes then
    checked (base ++ `nonmax_primes)
      (← `(($support).primes.image (fun p : Nat.Primes => (p : ℕ)) = ($ps).toFinset))
      (← `(by first | rfl | exact of_decide_eq_true (by rfl) | decide +kernel))
  if let some n := radical then
    checked (base ++ `nonmax_rad) (← `($n = ($support).primes.prod (fun p => (p : ℕ))))
      (← `(by first | rfl | decide +kernel))

/-- Check the row encoding and compare it with the full finite-level Galois image. -/
def certifyAdelicGenerators (base : Name) : CommandElabM Unit := do
  let some report ← bindStored base `adelicGenerators `adelic_gens (← `(AdelicGeneratorsClaim))
    | return
  checked (base ++ `adelic_gens_shape)
    (← `(0 < ($report).modulus ∧
      ($report).rows.all (fun (a, b, c, d) => decide
        (a < ($report).modulus ∧ b < ($report).modulus ∧
          c < ($report).modulus ∧ d < ($report).modulus)) = true))
    (← `(by decide +kernel))
  let some proof ← suppliedProof base `adelicGenerators
    | logInfo m!"Unverified {base} adelic_gens: supply the complete finite-level image evidence"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `adelic_generator_fact)
  emit (← `(def $fact : @FiniteGaloisImageFact $curve inferInstance (Classical.decEq _) :=
    $proof))
  auditAxioms (base ++ `adelic_generator_fact)
  checked (base ++ `adelic_gens)
    (← `((($fact).modulus : ℕ) = ($report).modulus ∧ ($fact).matrixRows = ($report).rows))
    (← `(by constructor <;> first | rfl | decide +kernel))

end VerifiedLcalc.CertifyEC
