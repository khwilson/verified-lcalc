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

/-- Compare a reported natural invariant with the corresponding optional proof data. -/
private def checkAdelicNat (base field : Name) (report : Option Ident)
    (actual : TSyntax `term) : CommandElabM Bool := do
  let some value := report | return false
  unless ← hasOptionalProof actual field do
    logInfo m!"Unverified {base} {field}: supply a proof of this adelic invariant"
    return false
  checked (base ++ field) (← `($actual = some $value))
    (← `(by first | rfl | exact of_decide_eq_true (by rfl) | decide +kernel))
  return true

/-- Recognize the incomplete four-component producer format for verification dispatch. -/
private def parsePartialAdelicLabel (label : Ident) :
    CommandElabM (Option (ℕ × ℕ × ℕ)) :=
  runTermElabM fun _ => do
    let expr ← Term.elabTerm (← `(($label).2)) (some (mkConst ``String))
    let .lit (.strVal value) ← Lean.Meta.whnf expr
      | throwError "Expected a closed adelic image label"
    match value.splitOn "." with
    | [n, i, g, "?"] =>
      let (some level, some index, some genus) := (n.toNat?, i.toNat?, g.toNat?)
        | throwError "Expected natural level, index and genus in the partial adelic label"
      return some (level, index, genus)
    | _ => return none

/-- Check the reported adelic invariants against one simultaneous adelic-image attachment. -/
private def certifyAdelicImage (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let level ← bindStored base `adelicLevel `adelic_level (← `(ℕ))
  let index ← bindStored base `adelicIndex `adelic_index (← `(ℕ))
  let genus ← bindStored base `adelicGenus `adelic_genus (← `(ℕ))
  let label ← bindStored base `adelicImage `adelic_image (← `(ℕ × String))
  if let some level := level then
    checked (base ++ `adelic_level_positive) (← `(0 < $level)) (← `(by decide +kernel))
  if let some index := index then
    checked (base ++ `adelic_index_positive) (← `(0 < $index)) (← `(by decide +kernel))
  let partialReport ← match label with
    | none => pure none
    | some label => do
      checked (base ++ `adelic_image_prime) (← `(($label).1 = 0)) (← `(by decide +kernel))
      if let some values ← parsePartialAdelicLabel label then
        pure (some (label, values))
      else
        logInfo m!"Unverified {base} adelic_image: the conjugacy-class suffix is unsupported"
        pure none
  if level.isNone && index.isNone && genus.isNone && partialReport.isNone then return
  let some proof ← attachedFact attachment `adelicImage
    | logInfo m!"Unverified {base} adelic data: supply the exact simultaneous image"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `adelic_image_fact)
  emit (← `(def $fact : @AdelicImageFact $curve inferInstance (Classical.decEq _) := $proof))
  auditAxioms (base ++ `adelic_image_fact)
  let actualLevel ← `((($fact).level.map fun n => (n.val : ℕ)))
  let actualIndex ← `((($fact).index.map fun i => (i.val : ℕ)))
  let actualGenus ← `((($fact).genus.map AdelicGenusFact.genus))
  let checkedLevel ← checkAdelicNat base `adelic_level level actualLevel
  let checkedIndex ← checkAdelicNat base `adelic_index index actualIndex
  let checkedGenus ← checkAdelicNat base `adelic_genus genus actualGenus
  let mut labelTerm ← `(none)
  let mut checkedLabel := false
  if let some (label, n, i, g) := partialReport then
    let formatted ← `(formatPartialAdelicImageOf $actualLevel $actualIndex $actualGenus)
    if ← hasOptionalProof formatted `adelic_image then
      let reportLevel := quote n
      let reportIndex := quote i
      let reportGenus := quote g
      let levels := base ++ `adelic_image_level
      let indices := base ++ `adelic_image_index
      let genera := base ++ `adelic_image_genus
      for (name, actual, value) in
          [(levels, actualLevel, reportLevel), (indices, actualIndex, reportIndex),
            (genera, actualGenus, reportGenus)] do
        checked name (← `($actual = some $value))
          (← `(by first | rfl | exact of_decide_eq_true (by rfl) | decide +kernel))
      let levelEq := rootIdent levels
      let indexEq := rootIdent indices
      let genusEq := rootIdent genera
      let formatting := base ++ `adelic_image_format
      checked formatting
        (← `(formatPartialAdelicImage $reportLevel $reportIndex $reportGenus = ($label).2))
        (← `(by
          unfold formatPartialAdelicImage $label
          apply String.toList_injective
          simp [Nat.toDigits_eq_ite (by decide : 1 < 10)]))
      let formatEq := rootIdent formatting
      checked (base ++ `adelic_image) (← `($formatted = some ($label).2))
        (← `(by
          rw [($levelEq), ($indexEq), ($genusEq)]
          exact congrArg some $formatEq))
      let eq := rootIdent (base ++ `adelic_image)
      labelTerm ← `(some ⟨($label).2, $eq⟩)
      checkedLabel := true
    else
      logInfo m!"Unverified {base} adelic_image: supply proofs of level, index and genus"
  if checkedLevel || checkedIndex || checkedGenus || checkedLabel then
    let certificate := rootIdent (base ++ `adelic_image_certificate)
    emit (← `(def $certificate :
      @AdelicImageCertificate $curve inferInstance (Classical.decEq _) :=
      { facts := $fact, partialLabel := $labelTerm }))
    auditAxioms (base ++ `adelic_image_certificate)

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

/-- Check one local row against an exact prime-adic conjugacy class. -/
private def certifyPadicImage (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `padicImage `elladic_image (← `(ℕ × String))
    | return
  checked (base ++ `elladic_image_prime) (← `(Nat.Prime ($report).1)) (← `(by decide +kernel))
  let some proof ← attachedFact attachment `padicImage
    | logInfo m!"Unverified {base} elladic_image: supply the exact prime-adic subgroup comparison"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `elladic_image_fact)
  emit (← `(def $fact : @PadicImageLabelFact $curve inferInstance (Classical.decEq _) := $proof))
  auditAxioms (base ++ `elladic_image_fact)
  checked (base ++ `elladic_image)
    (← `(((($fact).prime : ℕ), ($fact).label) = $report))
    (← `(by first | rfl | decide +kernel))

/-- Check every submitted prime-adic label and exclude repeated primes. -/
private def certifyPadicImages (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `padicImages `elladic_images (← `(List String))
    | return
  let some proof ← attachedFact attachment `padicImages
    | logInfo m!"Unverified {base} elladic_images: supply exact prime-adic subgroup comparisons"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `elladic_images_fact)
  emit (← `(def $fact : @PadicImageListFact $curve inferInstance (Classical.decEq _) := $proof))
  auditAxioms (base ++ `elladic_images_fact)
  checked (base ++ `elladic_images)
    (← `((($fact).entries.map PadicImageLabelFact.label) = $report))
    (← `(by first | rfl | decide +kernel))
  checked (base ++ `elladic_images_distinct_primes)
    (← `(((($fact).entries.map fun entry => (entry.prime : ℕ)).Nodup)))
    (← `(by first | exact of_decide_eq_true (by rfl) | decide +kernel))

/-- Bind the full reported list to the verified sublist. -/
private def certifyModulusImages (base : Name) (attachment : Option Ident) :
    CommandElabM Unit := do
  let some report ← bindStored base `modulusImages `modm_images (← `(List String))
    | return
  let some proof ← attachedFact attachment `modulusImages
    | logInfo m!"Unverified {base} modm_images: supply exact finite subgroup comparisons"
  let curve := rootIdent (base ++ `curve)
  let fact := rootIdent (base ++ `modm_images_fact)
  emit (← `(def $fact : @ModulusImageListFact $curve inferInstance (Classical.decEq _) := $proof))
  auditAxioms (base ++ `modm_images_fact)
  let sourceEq := rootIdent (base ++ `modm_images_source)
  checked (base ++ `modm_images_source)
    (← `(($fact).reported = $report))
    (← `(by first | rfl | decide +kernel))
  let labels ← `((($fact).entries.map ModulusImageLabelFact.label))
  checked (base ++ `modm_images) (← `(($labels).Sublist $report))
    (← `(by
      rw [← ($sourceEq)]
      exact ($fact).sublist))
  if ← hasOptionalProof (← `(($fact).allEntries)) `modm_images then
    checked (base ++ `modm_images_all) (← `($labels = $report))
      (← `(by
        exact (($fact).allEntries.get (by rfl)).down.trans $sourceEq))

/-- Check the Galois report fields against any matching evidence in `with_proofs`. -/
def certifyGaloisFacts (base : Name) (attachment : Option Ident) : CommandElabM Unit := do
  certifyNonmaxPrimes base attachment
  certifyAdelicGenerators base attachment
  certifyAdelicImage base attachment
  certifyModPrimeImage base attachment
  certifyModPrimeImages base attachment
  certifyPadicImage base attachment
  certifyPadicImages base attachment
  certifyModulusImages base attachment

end VerifiedLcalc.CertifyEC
