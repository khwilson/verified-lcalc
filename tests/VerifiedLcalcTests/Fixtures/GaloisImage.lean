/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-! # Exact finite Galois image and conditional exceptional primes -/

@[expose] public section

namespace VerifiedLcalcTests.GaloisImage

open VerifiedLcalc
open WeierstrassCurve
open scoped Matrix

/-- The integral equation of `y² = x³ - x`. -/
abbrev model : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 0⟩
/-- The rational curve. -/
abbrev E := model.baseChange ℚ

/-- The geometric base field of the fixture. -/
abbrev K := AlgebraicClosure ℚ

/-- The geometric base change of the fixture. -/
noncomputable abbrev W := E.baseChange K

instance : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

attribute [local instance] Classical.decEq

private theorem fixes_split_two {a b r s t : ℤ}
    (factorization : ∀ x : K, x ^ 3 + (a : K) * x + b = (x - r) * (x - s) * (x - t))
    (σ : K ≃ₐ[ℚ] K)
    (P : AddSubgroup.torsionBy
      (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).baseChange K).toAffine.Point
      (2 : ℤ)) :
    Multiplicative.toAdd
      (((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).torsionGaloisAction 2 σ) P =
      P := by
  apply Subtype.ext
  rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply]
  obtain ⟨P, ht⟩ := P
  change Affine.Point.map σ.toAlgHom P = P
  cases P with
  | zero => exact map_zero _
  | some x y h =>
    have hadd : Affine.Point.some x y h + Affine.Point.some x y h = 0 := by
      change (2 : ℤ) • Affine.Point.some x y h = 0 at ht
      simpa only [two_zsmul] using ht
    have hy := (Affine.Point.some_add_self_eq_zero_iff h).mp hadd
    rw [Affine.evalEval_polynomialY] at hy
    have hy₂ : 2 * y = 0 := by simpa [baseChange] using hy
    have ey : y = 0 := (mul_eq_zero.mp hy₂).resolve_left two_ne_zero
    subst y
    have eqn : 0 = x ^ 3 + (a : K) * x + b := by
      simpa [baseChange] using (Affine.equation_iff _ _).mp h.1
    have hprod : (x - r) * (x - s) * (x - t) = 0 := (factorization x).symm.trans eqn.symm
    rw [Affine.Point.map_some, Affine.Point.some.injEq]
    simp only [AlgEquiv.coe_toAlgHom, map_zero, and_true]
    rcases mul_eq_zero.mp hprod with hh | hh
    · rcases mul_eq_zero.mp hh with hh | hh
      · simp [sub_eq_zero.mp hh]
      · simp [sub_eq_zero.mp hh]
    · simp [sub_eq_zero.mp hh]

/-- The full mod-2 action of a short equation with split cubic in rational coordinates. -/
def splitModTwoImage {a b r s t : ℤ}
    [((⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℤ).baseChange ℚ).IsElliptic]
    (factorization : ∀ x : K, x ^ 3 + (a : K) * x + b = (x - r) * (x - s) * (x - t)) :
    FiniteGaloisImageFact (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℤ) where
  modulus := 2
  generators := [1]
  correct := by
    let curve := (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℤ).baseChange ℚ
    let basis := (nonempty_basis_torsionBy (curve.baseChange K) 2 (by norm_num)).some
    refine ⟨basis, ?_⟩
    intro g
    change g ∈
        Subgroup.closure {a | a ∈ ([1] : List (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))} ↔
      ∃ σ : K ≃ₐ[ℚ] K, ∀ P,
        basis.equivFun (Multiplicative.toAdd (curve.torsionGaloisAction 2 σ) P) =
          g.val *ᵥ basis.equivFun P
    simp only [List.mem_singleton, Set.ofPred_eq_eq_singleton, Subgroup.closure_singleton_one]
    constructor
    · rintro rfl
      exact ⟨1, fun P => by
        rw [fixes_split_two factorization]
        exact (Matrix.one_mulVec _).symm⟩
    · rintro ⟨σ, h⟩
      apply Units.ext
      apply Matrix.mulVec_injective
      funext v
      obtain ⟨P, rfl⟩ := basis.equivFun.surjective v
      have hP := h P
      rw [fixes_split_two factorization] at hP
      change g.val *ᵥ basis.equivFun P =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ basis.equivFun P
      rw [Matrix.one_mulVec]
      exact hP.symm

/-- Every Galois matrix on the geometric 2-torsion is the identity. -/
def modTwoImage : FiniteGaloisImageFact model :=
  splitModTwoImage (r := 0) (s := 1) (t := -1) fun x => by push_cast; ring

certify_ec ExactModTwo from_json_string
  r#"{ "ainvs":[0,0,0,-1,0], "prime":0, "adelic_image":"2.6.0.?",
       "adelic_gens":[[1,0,0,1]], "discriminant":64, "integral_points":[[0,0]] }"#
  with_proofs ({ adelicGenerators := some modTwoImage } : IntegralCurveProofs model)

/-- LMFDB curve 40.a2, whose cubic splits at the rational roots −2, −1 and 3. -/
abbrev splitModel : WeierstrassCurve ℤ := ⟨0, 0, 0, -7, -6⟩

instance : (splitModel.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- The exact mod-2 image of 40.a2 matches Sutherland's split-Cartan label. -/
def splitModTwoLabel : ModPrimeImageFact splitModel where
  finiteImage := splitModTwoImage (r := -2) (s := -1) (t := 3) fun x => by push_cast; ring
  prime := Nat.prime_two
  label := "2Cs"
  conjugate := by
    refine ⟨[(1, 0, 0, 1)], rfl, 1, ?_⟩
    change Subgroup.closure {g | g ∈ ([1] : List (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))} =
      (residualImageReferenceGroup 2 [(1, 0, 0, 1)]).map (MulAut.conj 1).toMonoidHom
    have hrow : galoisMatrixRow (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) =
        (1, 0, 0, 1) := by decide +kernel
    rw [residualImageReferenceGroup, ← hrow]
    simp only [List.mem_singleton, galoisMatrixRow_injective.eq_iff, Set.ofPred_eq_eq_singleton,
      Subgroup.closure_singleton_one, Subgroup.map_bot]

/-- Attach the exact image independently to either of the two reporting fields. -/
def splitModTwoAttachment : IntegralCurveProofs splitModel :=
  { modPrimeImage := some splitModTwoLabel
    modPrimeImages := some { images := [splitModTwoLabel] } }

certify_ec Residual40 from_json_string
  r#"{ "ainvs":[0,0,0,-7,-6], "prime":2, "modell_image":"2Cs", "modell_images":["2Cs"],
       "discriminant":6400, "integral_points":[[-2,0]] }"#
  with_proofs splitModTwoAttachment

certify_ec Residual40Lean from {
  equation := splitModel
  modPrimeImage := some (2, "2Cs")
  modPrimeImages := some ["2Cs"]
} with_proofs splitModTwoAttachment

/-- Reuse the proved split 2-torsion action for its native modular-curve label. -/
def splitModulusLabel : ModulusImageLabelFact splitModel where
  exactImage := splitModTwoLabel.finiteImage
  label := "2.6.0.a.1"
  correct := by
    left
    obtain ⟨rows, hr, hc⟩ := splitModTwoLabel.conjugate
    change some (2, [(1, 0, 0, 1)]) = some (2, rows) at hr
    exact ⟨rows, hr, hc⟩

/-- The real finite-image list for 40.a2. -/
def modm40Report : List String :=
  ["2.6.0.a.1", "4.24.0-4.a.1.1", "8.48.0-8.g.1.1", "20.48.0-20.b.1.1", "40.192.3-40.bk.1.5"]

/-- The verified sublist contains the level-two label. -/
def modm40Attachment : IntegralCurveProofs splitModel where
  modulusImages := some {
    reported := modm40Report
    entries := [splitModulusLabel]
    sublist := by
      change ["2.6.0.a.1"].Sublist modm40Report
      exact List.Sublist.cons_cons _ (List.nil_sublist _)
    hasEvidence := .inr (by simp) }

certify_ec Modulus40 from_json_string
  r#"{ "ainvs":[0,0,0,-7,-6], "modm_images":["2.6.0.a.1", "4.24.0-4.a.1.1", "8.48.0-8.g.1.1",
       "20.48.0-20.b.1.1", "40.192.3-40.bk.1.5"] }"#
  with_proofs modm40Attachment

/-- The integral equation of 69.a1. -/
abbrev padic69Model : WeierstrassCurve ℤ := ⟨1, 0, 1, -16, -25⟩

instance : (padic69Model.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- Geometric input for the exact 2-adic image and non-CM support of 69.a1. -/
class CataloguePadic69
    (action : outParam (PadicGaloisImageFact padic69Model ⟨2, Nat.prime_two⟩)) : Prop where
  /-- The full image is conjugate to the inverse image of a mod-2 Borel. -/
  conjugate : ∃ c : Matrix.GeneralLinearGroup (Fin 2) (AdelicLocalRing ⟨2, Nat.prime_two⟩),
    action.image = ((residualImageReferenceGroup 2 [(1, 1, 0, 1)]).comap
      (localImageReduction ⟨2, Nat.prime_two⟩ 1)).map (MulAut.conj c).toMonoidHom
  /-- The represented curve has geometric endomorphism ring ℤ. -/
  nonCM : ¬ (padic69Model.baseChange ℚ).HasGeometricCM
  /-- The entire exceptional integral support consists of the prime two. -/
  complete : ∀ p : Nat.Primes, ∃ image : PadicGaloisImageFact padic69Model p,
    p ∈ ([⟨2, Nat.prime_two⟩] : List Nat.Primes).toFinset ↔ image.image ≠ ⊤

/-- Attach the sourced 69.a1 comparison and the independent support proof. -/
def padic69Attachment {action : PadicGaloisImageFact padic69Model ⟨2, Nat.prime_two⟩}
    (h : CataloguePadic69 action) : IntegralCurveProofs padic69Model :=
  let row : PadicImageLabelFact padic69Model :=
    ⟨⟨2, Nat.prime_two⟩, action, "2.3.0.1", ⟨1, [(1, 1, 0, 1)], rfl, h.conjugate⟩⟩
  { padicImage := some row
    padicImages := some {
      entries := [row]
      coverage := some ⟨⟨h.nonCM, _, h.complete⟩, rfl⟩ } }

section

variable {action : PadicGaloisImageFact padic69Model ⟨2, Nat.prime_two⟩}
  [h : CataloguePadic69 action]

certify_ec PadicRow69 from_json_string
  r#"{ "ainvs":[1,0,1,-16,-25], "prime":2, "elladic_image":"2.3.0.1" }"#
  with_proofs (padic69Attachment h)

certify_ec PadicList69 from_json_string
  r#"{ "ainvs":[1,0,1,-16,-25], "elladic_images":["2.3.0.1"] }"#
  with_proofs (padic69Attachment h)

certify_ec PadicLean69 from {
  equation := padic69Model
  padicImage := some (2, "2.3.0.1")
  padicImages := some ["2.3.0.1"]
} with_proofs (padic69Attachment h)

end

/-- The integral equation of 37.a1, whose source list of residual exceptions is empty. -/
abbrev emptyListModel : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

instance : (emptyListModel.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- Geometric evidence needed to conclude the absence of exceptional residual primes. -/
class EmptyListResidualImages (subject : outParam (WeierstrassCurve ℤ)) : Prop where
  /-- The model in the source row. -/
  equation_eq : subject = emptyListModel
  /-- The curve has no geometric complex multiplication. -/
  nonCM : ¬ (emptyListModel.baseChange ℚ).HasGeometricCM
  /-- Each prime-torsion action has full image. -/
  full : ∀ p : Nat.Primes, ∃ image : FiniteGaloisImageFact emptyListModel,
    (image.modulus : ℕ) = (p : ℕ) ∧ Subgroup.closure {g | g ∈ image.generators} = ⊤

/-- An empty report certifies exhaustiveness only with independent all-prime evidence. -/
def emptyListAttachment {subject : WeierstrassCurve ℤ} (h : EmptyListResidualImages subject) :
    IntegralCurveProofs emptyListModel where
  modPrimeImages := some {
    images := []
    coverage := some ⟨{
      nonCM := h.nonCM
      complete p := by
        obtain ⟨image, hp, himage⟩ := h.full p
        exact ⟨image, hp, by simp [himage]⟩ }⟩ }

section

variable {subject : WeierstrassCurve ℤ} [h : EmptyListResidualImages subject]

certify_ec EmptyResidual37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "modell_images":[] }"#
  with_proofs (emptyListAttachment h)

end

/-- Independent arithmetic and geometric inputs for the 37.a1 adelic row.
The exact image argument already identifies the simultaneous Galois action. -/
class CatalogueAdelic37 (exactImage : outParam (AdelicImageFact emptyListModel)) : Prop where
  /-- The image contains the full adelic congruence kernel at 74. -/
  kernel : (adelicReduction 74).ker ≤ exactImage.image
  /-- Every smaller positive modulus fails the kernel containment test. -/
  minimal : ∀ N : ℕ+, N < 74 → ∃ g ∈ (adelicReduction N).ker, g ∉ exactImage.image
  /-- The adelic image has exactly two cosets. -/
  cosets : Nonempty ((AdelicGL ⧸ exactImage.image) ≃ Fin 2)
  /-- The coarse modular curve has finite CW type. -/
  finiteCW : TauCeti.FiniteCWType (adelicProjectiveSubgroup exactImage.image).CompactifiedQuotient
  /-- The compactified projective quotient has Euler characteristic two. -/
  euler :
    letI := finiteCW
    TauCeti.eulerChar (adelicProjectiveSubgroup exactImage.image).CompactifiedQuotient = 2

/-- Assemble the 37.a1 attachment from the independent kernel, coset and surface premises. -/
def adelic37Attachment {exactImage : AdelicImageFact emptyListModel}
    (h : CatalogueAdelic37 exactImage) : IntegralCurveProofs emptyListModel := by
  have hi : exactImage.image.index = 2 := by
    obtain ⟨e⟩ := h.cosets
    simpa [Subgroup.index] using Nat.card_congr e
  letI : exactImage.image.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by simp [hi])
  exact { adelicImage := some {
    exactImage with
    level := some ⟨74, h.kernel, fun N hN => by
      by_contra! hlt
      obtain ⟨g, hg, hnot⟩ := h.minimal N hlt
      exact hnot (hN hg)⟩
    index := some ⟨2, hi⟩
    genus := some {
      modulus := 74
      kernel := h.kernel
      finiteIndex := inferInstanceAs (exactImage.image.comap adelicSL2).FiniteIndex
      finiteCW := h.finiteCW
      genus := 0
      correct := by simpa using h.euler } } }

section

variable {exactImage : AdelicImageFact emptyListModel} [h : CatalogueAdelic37 exactImage]

certify_ec Adelic37 from {
  equation := emptyListModel
  adelicLevel := some 74
  adelicIndex := some 2
  adelicGenus := some 0
  adelicImage := some (0, "74.2.0.?")
  discriminant := some 37
} with_proofs (adelic37Attachment h)

certify_ec AdelicLevel37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "adelic_level":74 }"#
  with_proofs (adelic37Attachment h)

certify_ec AdelicIndex37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "adelic_index":2 }"#
  with_proofs (adelic37Attachment h)

certify_ec AdelicGenus37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "adelic_genus":0 }"#
  with_proofs (adelic37Attachment h)

certify_ec PartialAdelic37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "prime":0, "adelic_image":"74.2.0.?" }"#
  with_proofs (adelic37Attachment h)

certify_ec UnsupportedAdelic37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "prime":0, "adelic_image":"74.2.0.a.1" }"#
  with_proofs (adelic37Attachment h)

end

/-- Independent evidence that the exact mod-74 action gives the same inverse image as
the simultaneously proved adelic image of 37.a1. -/
class CatalogueModulus37 (action : outParam (FiniteGaloisImageFact emptyListModel))
    (adelic : outParam (AdelicImageFact emptyListModel)) : Prop
    extends CatalogueAdelic37 adelic where
  /-- The exact finite representation is on 74-torsion. -/
  modulus : action.modulus = 74
  /-- The full inverse image of its finite image is the proved adelic subgroup. -/
  lift : (Subgroup.closure {g | g ∈ action.generators}).comap
    (adelicReduction action.modulus) = adelic.image

/-- Certify the whole singleton finite-image report of 37.a1, with its suffix unspecified. -/
def modm37Attachment {action : FiniteGaloisImageFact emptyListModel}
    {adelic : AdelicImageFact emptyListModel} (h : CatalogueModulus37 action adelic) :
    IntegralCurveProofs emptyListModel := by
  let adelicFacts := (adelic37Attachment h.toCatalogueAdelic37).adelicImage.get (by rfl)
  let row : ModulusImageLabelFact emptyListModel := {
    exactImage := action
    label := "74.2.0.?"
    correct := by
      right
      let hg : AdelicGenusFact
          ((Subgroup.closure {g | g ∈ action.generators}).comap (adelicReduction action.modulus)) :=
        h.lift ▸ adelicFacts.genus.get (by rfl)
      refine ⟨2, hg, ?_, ?_, ?_⟩
      · rw [h.lift, h.modulus]
        exact (adelicFacts.level.get (by rfl)).property
      · have hi := congrArg Subgroup.index h.lift
        rw [Subgroup.index_comap_of_surjective _ (adelicReduction_surjective action.modulus)] at hi
        exact hi.trans (adelicFacts.index.get (by rfl)).property
      · have castGenus {H K : Subgroup AdelicGL} (e : H = K) (g : AdelicGenusFact K) :
            (e ▸ g : AdelicGenusFact H).genus = g.genus := by
          cases e
          rfl
        have genusZero : hg.genus = 0 := (castGenus h.lift _).trans rfl
        rw [genusZero, h.modulus]
        unfold formatPartialAdelicImage
        apply String.toList_injective
        simp [Nat.toDigits_eq_ite (by decide : 1 < 10)] }
  exact { modulusImages := some {
    reported := ["74.2.0.?"]
    entries := [row]
    sublist := List.Sublist.refl _
    hasEvidence := .inr (by simp)
    allEntries := some ⟨rfl⟩ } }

section

variable {action : FiniteGaloisImageFact emptyListModel} {adelic : AdelicImageFact emptyListModel}
  [h : CatalogueModulus37 action adelic]

certify_ec Modulus37 from_json_string
  r#"{ "ainvs":[0,0,1,-1,0], "modm_images":["74.2.0.?"] }"#
  with_proofs (modm37Attachment h)

end

/-- LMFDB curve 338.e1, whose two listed exceptional primes distinguish residual and
prime-adic maximality at 2. -/
abbrev catalogueModel : WeierstrassCurve ℤ := ⟨1, -1, 1, -65773, -6478507⟩

instance : (catalogueModel.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- The proposed exceptional support for the catalogue fixture. -/
def proposedSupport : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨7, Nat.prime_seven⟩}

/-- Exact exceptional-prime verification still needs geometric non-CM and intrinsic
image proofs at every prime of the represented curve. -/
class CatalogueLocalImages (curve : outParam (WeierstrassCurve ℤ)) : Prop where
  /-- The equation is the catalogue fixture's equation. -/
  equation_eq : curve = catalogueModel
  /-- The curve has geometric endomorphism ring ℤ. -/
  nonCM : ¬ (catalogueModel.baseChange ℚ).HasGeometricCM
  /-- The exact Tate-module image is proper precisely at 2 and 7. -/
  exactImages : ∀ p : Nat.Primes, ∃ image : PadicGaloisImageFact catalogueModel p,
    p ∈ proposedSupport ↔ image.image ≠ ⊤

/-- Assemble the catalogue fixture from explicit geometric premises. -/
def support338 {subject : WeierstrassCurve ℤ} (h : CatalogueLocalImages subject) :
    NonmaxPrimeSupportFact catalogueModel where
  nonCM := h.nonCM
  primes := proposedSupport
  complete := h.exactImages

/-- Attach the checked support evidence to the catalogue equation. -/
def nonmaxAttachment {subject : WeierstrassCurve ℤ} (h : CatalogueLocalImages subject) :
    IntegralCurveProofs catalogueModel :=
  { nonmaxSupport := some (support338 h) }

section

variable {subject : WeierstrassCurve ℤ} [h : CatalogueLocalImages subject]

certify_ec Exceptional338 from_json_string
  r#"{ "ainvs":[1,-1,1,-65773,-6478507], "nonmax_primes":[2,7], "nonmax_rad":14 }"#
  with_proofs (nonmaxAttachment h)

certify_ec Reordered338 from { equation := catalogueModel, nonmaxPrimes := some [7, 2] }
  with_proofs (nonmaxAttachment h)

certify_ec Radical338 from { equation := catalogueModel, nonmaxRadical := some 14 }
  with_proofs (nonmaxAttachment h)

end

end VerifiedLcalcTests.GaloisImage
