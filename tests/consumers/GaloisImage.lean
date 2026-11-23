/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
import VerifiedLcalcTests.Fixtures.GaloisImage
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
import Lean

/-! # Imported Galois image proofs, missing evidence and rollback -/

open VerifiedLcalc VerifiedLcalcTests.GaloisImage Lean Elab Command
open scoped Matrix

attribute [local instance] Classical.decEq

example : ExactModTwo.certificate.adelicGenerators = some ExactModTwo.adelic_generator_fact := rfl

example : ExactModTwo.claimed_adelic_gens.rows = [(1, 0, 0, 1)] := rfl

example : (ExactModTwo.certificate.adelicGenerators.get (by rfl)).modulus = 2 := rfl

example : (ExactModTwo.certificate.adelicGenerators.get (by rfl)).matrixRows =
    [(1, 0, 0, 1)] := ExactModTwo.adelic_gens.2

example : ∃ basis : Module.Basis (Fin 2) (ZMod 2)
    (AddSubgroup.torsionBy W.toAffine.Point ((2 : ℕ) : ℤ)),
    ∀ g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2),
      g = 1 ↔ ∃ σ : K ≃ₐ[ℚ] K, ∀ P,
        basis.equivFun (Multiplicative.toAdd (E.torsionGaloisAction ((2 : ℕ) : ℤ) σ) P) =
          g.val *ᵥ basis.equivFun P := by
  obtain ⟨basis, correct⟩ := (ExactModTwo.certificate.adelicGenerators.get (by rfl)).correct
  refine ⟨basis, fun g => ?_⟩
  have h := correct g
  change g ∈ Subgroup.closure
      {a | a ∈ ([1] : List (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))} ↔ _ at h
  simp only [List.mem_singleton, Set.ofPred_eq_eq_singleton, Subgroup.closure_singleton_one,
    Subgroup.mem_bot] at h
  exact h

section

variable {subject : WeierstrassCurve ℤ} [h : CatalogueLocalImages subject]

example : Exceptional338.certificate.nonmaxPrimes = some Exceptional338.nonmax_prime_support := rfl

example : ¬ (Exceptional338.curve.baseChange ℚ).HasGeometricCM :=
  (Exceptional338.certificate.nonmaxPrimes.get (by rfl)).nonCM

example (p : Nat.Primes) : ∃ image : PadicGaloisImageFact Exceptional338.curve p,
    p ∈ proposedSupport ↔ image.image ≠ ⊤ :=
  (Exceptional338.certificate.nonmaxPrimes.get (by rfl)).complete p

example : 14 = (Exceptional338.certificate.nonmaxPrimes.get (by rfl)).primes.prod
    (fun p => (p : ℕ)) := Exceptional338.nonmax_rad

example : Radical338.witness.nonmaxPrimes = none := rfl
example : Radical338.certificate.nonmaxPrimes.isSome = true := rfl

end

certify_ec ReportsOnly from_json_string
  r#"{ "ainvs":[0,0,0,-1,0], "nonmax_primes":[], "nonmax_rad":1,
       "adelic_level":2, "adelic_gens":[[1,0,0,1]] }"#

example : ReportsOnly.certificate.nonmaxPrimes = none := rfl
example : ReportsOnly.certificate.adelicGenerators = none := rfl
example : ReportsOnly.witness.nonmaxPrimes = some [] := rfl

private meta def rejectGalois (base : Name) (command : Syntax)
    (check : Option String := none) : CommandElabM Unit := do
  let messages := (← get).messages
  let mut failed := false
  try
    elabCommand command
    failed := (← get).messages.hasErrors
  catch err =>
    if let some label := check then
      let message ← err.toMessageData.toString
      unless (message.splitOn s!"failed checking {base}.{label}").length > 1 do
        throwError "Expected {base}.{label} to fail, got {message}"
    failed := true
  let env ← getEnv
  set { (← get) with messages }
  unless failed do throwError "Wrong Galois claim accepted: {base}"
  for suffix in [`curve, `witness, `integral_proofs, `claimed_nonmax_primes,
      `nonmax_prime_support, `nonmax_primes, `nonmax_rad,
      `claimed_adelic_gens, `adelic_generator_fact, `adelic_gens, `certificate] do
    if env.contains (base ++ suffix) then throwError "Rejected report leaked {base ++ suffix}"

run_cmd do
  for suffix in [`nonmax_primes, `nonmax_rad, `adelic_gens] do
    if (← getEnv).contains (`ReportsOnly ++ suffix) then
      throwError "Bare Galois report emitted an assertion for {suffix}"
  rejectGalois `DuplicatePrimes (← `(certify_ec DuplicatePrimes from
    { equation := model, nonmaxPrimes := some [2, 2] })) (some "nonmax_primes_shape")
  rejectGalois `WrongEncoding (← `(certify_ec WrongEncoding from_json_string
    r#"{ "ainvs":[0,0,0,-1,0], "adelic_level":2, "adelic_gens":[[1,0,0]] }"#))
  rejectGalois `CompositePrime (← `(certify_ec CompositePrime from
    { equation := model, nonmaxPrimes := some [4] })) (some "nonmax_primes_shape")
  rejectGalois `WrongRow (← `(certify_ec WrongRow from_json_string
    r#"{ "ainvs":[0,0,0,-1,0], "prime":2, "adelic_level":2, "adelic_gens":[] }"#))
  rejectGalois `ConflictingModuli (← `(certify_ec ConflictingModuli from_json_string
    r#"{ "ainvs":[0,0,0,-1,0], "adelic_level":3, "adelic_image":"2.6.0.?", "adelic_gens":[] }"#))
  rejectGalois `WrongModulus (← `(certify_ec WrongModulus from
    { equation := model, adelicGenerators := some ⟨3, [(1, 0, 0, 1)]⟩ }
      with_proofs ({ adelicGenerators := some modTwoImage } : IntegralCurveProofs model)))
    (some "adelic_gens")
  rejectGalois `WrongMatrix (← `(certify_ec WrongMatrix from_json_string
    r#"{ "ainvs":[0,0,0,-1,0], "adelic_level":2, "adelic_gens":[[1,1,0,1]] }"#
      with_proofs ({ adelicGenerators := some modTwoImage } : IntegralCurveProofs model)))
    (some "adelic_gens")

section

variable {subject : WeierstrassCurve ℤ} [h : CatalogueLocalImages subject]

run_cmd do
  rejectGalois `MissingPrime (← `(certify_ec MissingPrime from
    { equation := catalogueModel, nonmaxPrimes := some [7] }
      with_proofs (nonmaxAttachment h)))
    (some "nonmax_primes")
  rejectGalois `ExtraPrime (← `(certify_ec ExtraPrime from
    { equation := catalogueModel, nonmaxPrimes := some [2, 3, 7] }
      with_proofs (nonmaxAttachment h)))
    (some "nonmax_primes")
  rejectGalois `WrongRadical (← `(certify_ec WrongRadical from
    { equation := catalogueModel, nonmaxPrimes := some [2, 7], nonmaxRadical := some 28 }
      with_proofs (nonmaxAttachment h)))
    (some "nonmax_rad")

end

run_cmd do
  for declaration in [``modTwoImage, ``support338, ``ExactModTwo.certificate,
      ``ExactModTwo.adelic_gens, ``Exceptional338.certificate, ``Exceptional338.nonmax_primes,
      ``Reordered338.nonmax_primes,
      ``Exceptional338.nonmax_rad] do
    for assumption in ← liftTermElabM (Lean.collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected Galois-image axiom: {assumption}"
