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

example : Residual40.certificate.modPrimeImage = some Residual40.modell_image_fact := rfl

example :
    let entry := Residual40.certificate.modPrimeImage.get (by rfl)
    (((entry.finiteImage.modulus : ℕ), entry.label) = (2, "2Cs")) :=
  Residual40.modell_image

/-- The imported 40.a2 certificate identifies the subgroup of the exact mod-2 image. -/
theorem residual40_conjugate :
    let entry := Residual40.certificate.modPrimeImage.get (by rfl)
    ∃ c : Matrix.GeneralLinearGroup (Fin 2) (ZMod (entry.finiteImage.modulus : ℕ)),
      Subgroup.closure {g | g ∈ entry.finiteImage.generators} =
        (residualImageReferenceGroup (entry.finiteImage.modulus : ℕ) [(1, 0, 0, 1)]).map
          (MulAut.conj c).toMonoidHom := by
  obtain ⟨rows, hr, conjugate⟩ := (Residual40.certificate.modPrimeImage.get (by rfl)).conjugate
  change some (2, [(1, 0, 0, 1)]) = some (2, rows) at hr
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hr
  simpa [← hr] using conjugate

/-- Every submitted label in the 40.a2 curve-level list has a checked image. -/
theorem residual40_list_entry (label : String) (h : label ∈ Residual40.claimed_modell_images) :
    let list := Residual40.certificate.modPrimeImages.get (by rfl)
    ∃ entry ∈ list.images, entry.label = label := by
  apply ModPrimeImageListFact.exists_of_mem_labels
  change label ∈ Residual40.modell_images_fact.images.map ModPrimeImageFact.label
  rw [Residual40.modell_images]
  exact h

example : (Residual40.certificate.modPrimeImages.get (by rfl)).coverage = none := rfl

example : Residual40Lean.claimed_modell_image = Residual40.claimed_modell_image := rfl
example : Residual40Lean.claimed_modell_images = Residual40.claimed_modell_images := rfl

/-- With geometric evidence, the empty 37.a1 list proves surjectivity at every prime. -/
theorem residual37_surjective {subject : WeierstrassCurve ℤ} [h : EmptyListResidualImages subject]
    (p : Nat.Primes) :
    ∃ image : FiniteGaloisImageFact EmptyResidual37.curve,
      (image.modulus : ℕ) = (p : ℕ) ∧ Subgroup.closure {g | g ∈ image.generators} = ⊤ := by
  obtain ⟨image, hp, hproper⟩ :=
    (((EmptyResidual37.certificate (h := h)).modPrimeImages.get (by rfl)).coverage.get
      (by rfl)).down.complete p
  refine ⟨image, hp, not_ne_iff.mp fun hne => ?_⟩
  obtain ⟨entry, he, _⟩ := hproper.mpr hne
  change entry ∈ ([] : List _) at he
  exact List.not_mem_nil he

section

variable {exactImage : AdelicImageFact emptyListModel} [h : CatalogueAdelic37 exactImage]

/-- The imported certificate identifies the genuine minimal congruence level. -/
theorem adelic37_minimal_level :
    IsLeast {N : ℕ+ | (adelicReduction N).ker ≤ exactImage.image} 74 :=
  let facts := ((AdelicLevel37.certificate (h := h)).adelicImage.get (by rfl)).facts
  (facts.level.get (by rfl)).property

/-- The same certificate identifies the full inverse image of the finite reduction. -/
theorem adelic37_full_preimage :
    (exactImage.image.map (adelicReduction 74)).comap (adelicReduction 74) = exactImage.image :=
  adelic_comap_map_eq (adelic37_minimal_level (h := h)).1

/-- The index statement concerns the full integral adelic subgroup. -/
theorem adelic37_index : exactImage.image.index = 2 :=
  let facts := ((AdelicIndex37.certificate (h := h)).adelicImage.get (by rfl)).facts
  (facts.index.get (by rfl)).property

/-- The group's finite reduction at its proved level has the reported index. -/
theorem adelic37_finite_index : (exactImage.image.map (adelicReduction 74)).index = 2 :=
  (adelicReduction_index_eq (adelic37_minimal_level (h := h)).1).trans
    (adelic37_index (h := h))

/-- The genus statement concerns the compactified effective projective quotient. -/
theorem adelic37_genus :
    let gen := ((AdelicGenus37.certificate (h := h)).adelicImage.get (by rfl)).facts.genus.get
      (by rfl)
    letI := gen.finiteCW
    TauCeti.RiemannSurface.genus (adelicProjectiveSubgroup exactImage.image).CompactifiedQuotient =
      0 :=
  (((AdelicGenus37.certificate (h := h)).adelicImage.get (by rfl)).facts.genus.get
    (by rfl)).genus_eq

/-- The native label with no numeric fields decodes and certifies exactly the formatted prefix. -/
theorem adelic37_partial_label :
    let checked := (PartialAdelic37.certificate (h := h)).adelicImage.get (by rfl)
    (checked.partialLabel.get (by rfl)).val = formatPartialAdelicImage 74 2 0 :=
  rfl

example : PartialAdelic37.witness.adelicLevel = none := rfl
example : PartialAdelic37.witness.adelicIndex = none := rfl
example : PartialAdelic37.witness.adelicGenus = none := rfl
example : UnsupportedAdelic37.certificate.adelicImage = none := rfl

end

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
       "adelic_level":2, "adelic_gens":[[1,0,0,1]], "prime":0,
       "modell_images":[] }"#

example : ReportsOnly.certificate.nonmaxPrimes = none := rfl
example : ReportsOnly.certificate.adelicGenerators = none := rfl
example : ReportsOnly.witness.nonmaxPrimes = some [] := rfl
example : ReportsOnly.certificate.modPrimeImages = none := rfl
example : ReportsOnly.witness.modPrimeImages = some [] := rfl

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
      `claimed_adelic_gens, `adelic_generator_fact, `adelic_gens,
      `claimed_modell_image, `modell_image_fact, `modell_image,
      `claimed_modell_images, `modell_images_fact, `modell_images,
      `claimed_adelic_image, `adelic_image_fact, `adelic_image, `adelic_image_certificate,
      `claimed_adelic_level, `claimed_adelic_index, `claimed_adelic_genus, `certificate] do
    if env.contains (base ++ suffix) then throwError "Rejected report leaked {base ++ suffix}"

run_cmd do
  for suffix in [`nonmax_primes, `nonmax_rad, `adelic_gens, `modell_images] do
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
  rejectGalois `WrongResidualLabel (← `(certify_ec WrongResidualLabel from
    { equation := splitModel, modPrimeImage := some (2, "2B") }
      with_proofs splitModTwoAttachment)) (some "modell_image")
  rejectGalois `WrongResidualPrime (← `(certify_ec WrongResidualPrime from
    { equation := splitModel, modPrimeImage := some (3, "2Cs") }
      with_proofs splitModTwoAttachment)) (some "modell_image")
  rejectGalois `MissingResidualPrime (← `(certify_ec MissingResidualPrime from_json_string
    r#"{ "ainvs":[0,0,0,-7,-6], "modell_image":"2Cs" }"#))
  rejectGalois `AdelicResidualPrime (← `(certify_ec AdelicResidualPrime from_json_string
    r#"{ "ainvs":[0,0,0,-7,-6], "prime":0, "modell_image":"2Cs" }"#))
    (some "modell_image_prime")
  rejectGalois `WrongResidualList (← `(certify_ec WrongResidualList from_json_string
    r#"{ "ainvs":[0,0,0,-7,-6], "modell_images":[] }"#
      with_proofs splitModTwoAttachment)) (some "modell_images")
  rejectGalois `DuplicateResidualPrime (← `(certify_ec DuplicateResidualPrime from
    { equation := splitModel, modPrimeImages := some ["2Cs", "2Cs"] }
      with_proofs ({ modPrimeImages := some { images := [splitModTwoLabel, splitModTwoLabel] } } :
        IntegralCurveProofs splitModel))) (some "modell_images_distinct_primes")


section

variable {exactImage : AdelicImageFact emptyListModel} [h : CatalogueAdelic37 exactImage]

run_cmd do
  let env ← getEnv
  if env.contains `VerifiedLcalcTests.GaloisImage.UnsupportedAdelic37.adelic_image then
    throwError "Unsupported adelic class suffix produced a checked label"
  rejectGalois `IncorrectAdelicPrefix (← `(certify_ec IncorrectAdelicPrefix from_json_string
    r#"{ "ainvs":[0,0,1,-1,0], "prime":0, "adelic_image":"74.3.0.?" }"#
      with_proofs (adelic37Attachment h))) (some "adelic_image")
  rejectGalois `IncorrectAdelicLevel (← `(certify_ec IncorrectAdelicLevel from_json_string
    r#"{ "ainvs":[0,0,1,-1,0], "adelic_level":37 }"#
      with_proofs (adelic37Attachment h))) (some "adelic_level")
  rejectGalois `IncorrectAdelicIndex (← `(certify_ec IncorrectAdelicIndex from_json_string
    r#"{ "ainvs":[0,0,1,-1,0], "adelic_index":3 }"#
      with_proofs (adelic37Attachment h))) (some "adelic_index")
  rejectGalois `IncorrectAdelicGenus (← `(certify_ec IncorrectAdelicGenus from_json_string
    r#"{ "ainvs":[0,0,1,-1,0], "adelic_genus":1 }"#
      with_proofs (adelic37Attachment h))) (some "adelic_genus")
  rejectGalois `NonzeroAdelicPrime (← `(certify_ec NonzeroAdelicPrime from_json_string
    r#"{ "ainvs":[0,0,1,-1,0], "prime":2, "adelic_image":"74.2.0.?" }"#))
    (some "adelic_image_prime")

end

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
      ``Exceptional338.nonmax_rad, ``Residual40.certificate, ``Residual40Lean.certificate,
      ``residual40_conjugate, ``residual40_list_entry, ``residual37_surjective,
      ``Adelic37.certificate, ``PartialAdelic37.certificate, ``adelic37_minimal_level,
      ``adelic37_full_preimage, ``adelic37_index, ``adelic37_finite_index, ``adelic37_genus,
      ``adelic37_partial_label] do
    for assumption in ← liftTermElabM (Lean.collectAxioms declaration) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected Galois-image axiom: {assumption}"
