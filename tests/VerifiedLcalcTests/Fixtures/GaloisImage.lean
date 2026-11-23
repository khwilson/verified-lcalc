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

private theorem fixes_two (σ : K ≃ₐ[ℚ] K)
    (P : AddSubgroup.torsionBy W.toAffine.Point (2 : ℤ)) :
    Multiplicative.toAdd (E.torsionGaloisAction 2 σ) P = P := by
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
    have hy₂ : 2 * y = 0 := by simpa [W, E, model, baseChange] using hy
    have ey : y = 0 := (mul_eq_zero.mp hy₂).resolve_left two_ne_zero
    subst y
    have eqn : 0 = x ^ 3 - x := by
      simpa [W, E, model, baseChange, sub_eq_add_neg] using (Affine.equation_iff _ _).mp h.1
    have hprod : x * (x - 1) * (x + 1) = 0 := by linear_combination -eqn
    rw [Affine.Point.map_some, Affine.Point.some.injEq]
    simp only [AlgEquiv.coe_toAlgHom, map_zero, and_true]
    rcases mul_eq_zero.mp hprod with hh | hh
    · rcases mul_eq_zero.mp hh with hh | hh
      · simp [hh]
      · simp [sub_eq_zero.mp hh]
    · simp [eq_neg_of_add_eq_zero_left hh]

/-- Every Galois matrix on the geometric 2-torsion is the identity. -/
def modTwoImage : FiniteGaloisImageFact model where
  modulus := 2
  generators := [1]
  correct := by
    let b := (nonempty_basis_torsionBy W 2 (by norm_num)).some
    refine ⟨b, ?_⟩
    intro g
    change Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) at g
    change g ∈
        Subgroup.closure {a | a ∈ ([1] : List (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))} ↔
      ∃ σ : K ≃ₐ[ℚ] K, ∀ P,
        b.equivFun (Multiplicative.toAdd (E.torsionGaloisAction 2 σ) P) = g.val *ᵥ b.equivFun P
    simp only [List.mem_singleton, Set.ofPred_eq_eq_singleton, Subgroup.closure_singleton_one,
      Subgroup.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, fun P => by rw [fixes_two]; simp⟩
    · rintro ⟨σ, h⟩
      apply Units.ext
      apply Matrix.mulVec_injective
      funext v
      obtain ⟨P, rfl⟩ := b.equivFun.surjective v
      simpa [fixes_two] using (h P).symm

certify_ec ExactModTwo from_json_string
  r#"{ "ainvs":[0,0,0,-1,0], "prime":0, "adelic_image":"2.6.0.?",
       "adelic_gens":[[1,0,0,1]], "discriminant":64, "integral_points":[[0,0]] }"#
  with_proofs ({ adelicGenerators := some modTwoImage } : IntegralCurveProofs model)

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
