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

/-- Check the exceptional prime list and radical against complete non-CM local image evidence. -/
private def certifyNonmaxPrimes (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let primes ← bindStored base `nonmaxPrimes `nonmax_primes (← `(List ℕ))
  let radical ← bindStored base `nonmaxRadical `nonmax_rad (← `(ℕ))
  if primes.isNone && radical.isNone then return
  if let some ps := primes then
    checked (base ++ `nonmax_primes_shape)
      (← `(($ps).Nodup ∧ ($ps).all (fun p => decide (Nat.Prime p)) = true))
      (← `(by decide +kernel))
  if let some n := radical then
    checked (base ++ `nonmax_rad_positive) (← `(0 < $n)) (← `(by decide +kernel))
  let some proof ← attachedFact attachment `nonmaxSupport
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
private def certifyAdelicGenerators (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `adelicGenerators `adelic_gens (← `(AdelicGeneratorsClaim))
    | return
  checked (base ++ `adelic_gens_shape)
    (← `(0 < ($report).modulus ∧
      ($report).rows.all (fun (a, b, c, d) => decide
        (a < ($report).modulus ∧ b < ($report).modulus ∧
          c < ($report).modulus ∧ d < ($report).modulus)) = true))
    (← `(by decide +kernel))
  let some proof ← attachedFact attachment `adelicGenerators
    | logInfo m!"Unverified {base} adelic_gens: supply the complete finite-level image evidence"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `adelic_generator_fact)
  emit (← `(def $fact : @FiniteGaloisImageFact $curve inferInstance (Classical.decEq _) :=
    $proof))
  auditAxioms (base ++ `adelic_generator_fact)
  checked (base ++ `adelic_gens)
    (← `((($fact).modulus : ℕ) = ($report).modulus ∧ ($fact).matrixRows = ($report).rows))
    (← `(by constructor <;> first | rfl | decide +kernel))

/-- Compare one source row with a proved residual conjugacy class. -/
private def certifyModPrimeImage (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `modPrimeImage `modell_image (← `(ℕ × String))
    | return
  checked (base ++ `modell_image_prime) (← `(Nat.Prime ($report).1))
    (← `(by decide +kernel))
  let some proof ← attachedFact attachment `modPrimeImage
    | logInfo m!"Unverified {base} modell_image: supply an exact residual image"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `modell_image_fact)
  emit (← `(def $fact :
    @ModPrimeImageFact $curve inferInstance (Classical.decEq _) := $proof))
  auditAxioms (base ++ `modell_image_fact)
  checked (base ++ `modell_image)
    (← `(((($fact).finiteImage.modulus : ℕ), ($fact).label) = $report))
    (← `(by first | rfl | decide +kernel))

/-- Compare the labels in order and rule out multiple entries at the same prime. -/
private def certifyModPrimeImages (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `modPrimeImages `modell_images (← `(List String))
    | return
  let some proof ← attachedFact attachment `modPrimeImages
    | logInfo m!"Unverified {base} modell_images: supply exact residual image evidence"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `modell_images_fact)
  emit (← `(def $fact :
    @ModPrimeImageListFact $curve inferInstance (Classical.decEq _) := $proof))
  auditAxioms (base ++ `modell_images_fact)
  checked (base ++ `modell_images)
    (← `((($fact).images.map ModPrimeImageFact.label) = $report))
    (← `(by first | rfl | decide +kernel))
  checked (base ++ `modell_images_distinct_primes)
    (← `(((($fact).images.map fun entry => (entry.finiteImage.modulus : ℕ)).Nodup)))
    (← `(by first | exact of_decide_eq_true (by rfl) | decide +kernel))

/-- Check the Galois report fields against any matching evidence in `with_proofs`. -/
def certifyGaloisFacts (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  certifyNonmaxPrimes base attachment
  certifyAdelicGenerators base attachment
  certifyModPrimeImage base attachment
  certifyModPrimeImages base attachment

end VerifiedLcalc.CertifyEC
