/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
import Mathlib.Data.List.OfFn

/-! ## Field presentations and ordered height witnesses -/

@[expose] public section

namespace VerifiedLcalc

open Polynomial

/-- If the coefficient list ends in a nonzero coefficient at the claimed index,
the decoded polynomial has the claimed degree. -/
theorem TorsionGrowthFieldClaim.natDegree_eq (claim : TorsionGrowthFieldClaim)
    (length : claim.coefficients.length = claim.degree + 1)
    (leading : claim.coefficients[claim.degree]?.getD 0 ≠ 0) :
    claim.polynomial.natDegree = claim.degree := by
  have h : claim.degree < claim.coefficients.length := by omega
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · have upper := ofFn_natDegree_lt (by omega : 1 ≤ claim.coefficients.length)
      (fun i => (claim.coefficients[i] : ℚ))
    rw [polynomial]
    omega
  · rw [polynomial, ofFn_coeff_eq_val_of_lt _ h]
    rw [List.getElem?_eq_getElem h, Option.getD_some] at leading
    exact_mod_cast leading

/-- The absolute degree of the field presented by the growth witness. -/
def TorsionGrowthFieldFact.degree {curve : WeierstrassCurve ℤ}
    (fact : TorsionGrowthFieldFact curve) : ℕ :=
  fact.polynomial.natDegree

/-- The absolute degree is the dimension of the field as a rational vector space. -/
theorem TorsionGrowthFieldFact.degree_eq {curve : WeierstrassCurve ℤ}
    (fact : TorsionGrowthFieldFact curve) :
    Module.finrank ℚ (AdjoinRoot fact.polynomial) = fact.degree :=
  finrank_quotient_span_eq_natDegree

/-- The full torsion equivalence in the indices and field presented by the submitted row. -/
noncomputable def StoredTorsionGrowthFact.equivalence {curve : WeierstrassCurve ℤ}
    (fact : StoredTorsionGrowthFact curve) :
    letI : Fact (Irreducible fact.field.polynomial) :=
      ⟨fact.polynomial_eq ▸ fact.presentation.irreducible⟩
    (∀ i : Fin fact.factors.length, ZMod (fact.factors.get i)) ≃+
      AddCommGroup.torsion
        (curve.baseChange (AdjoinRoot fact.field.polynomial)).toAffine.Point := by
  have alignFactors : (⟨fact.presentation.factorCount, fact.presentation.factor⟩ :
      Σ n : ℕ, Fin n → ℕ) = ⟨fact.factors.length, fact.factors.get⟩ :=
    List.ofFn_inj'.mp (fact.factors_eq.trans (List.ofFn_get fact.factors).symm)
  let transport (p : Polynomial ℚ) (hp : Irreducible p)
      (equal : fact.presentation.polynomial = p) (idx : Σ n : ℕ, Fin n → ℕ)
      (align : ⟨fact.presentation.factorCount, fact.presentation.factor⟩ = idx) :
      letI : Fact (Irreducible p) := ⟨hp⟩
      (∀ i, ZMod (idx.2 i)) ≃+ AddCommGroup.torsion
        (curve.baseChange (AdjoinRoot p)).toAffine.Point := by
    subst p
    subst idx
    exact fact.presentation.equivalence
  exact transport _ (fact.polynomial_eq ▸ fact.presentation.irreducible)
    fact.polynomial_eq _ alignFactors

/-- The affine coordinates of a rational point, with `none` for the point at infinity. -/
def CanonicalHeightFacts.pointCoordinates {curve : WeierstrassCurve ℚ}
    (point : curve.toAffine.Point) : Option (ℚ × ℚ) :=
  Option.map Subtype.val (curve.toAffine.nonsingularPointEquiv point)

/-- The ordered points built from checked affine coordinates recover those coordinates. -/
theorem CanonicalHeightFacts.pointCoordinates_ofFn_mk {curve : WeierstrassCurve ℚ}
    [curve.IsElliptic]
    (coordinates : List (ℚ × ℚ))
    (onCurve : ∀ x y, (x, y) ∈ coordinates → curve.toAffine.Equation x y) :
    List.ofFn (fun i : Fin coordinates.length =>
      pointCoordinates (.mk (onCurve _ _ (List.getElem_mem i.isLt)))) =
      coordinates.map some := by
  change List.ofFn (fun i : Fin coordinates.length => some coordinates[i]) = _
  exact List.ofFn_getElem_eq_map coordinates some

/-- Transfer indexed heights along equality of the entire ordered point list. -/
def CanonicalHeightFacts.ofPointListEq {curve : WeierstrassCurve ℚ} [curve.IsElliptic]
    {source target : Σ n : ℕ, Fin n → curve.toAffine.Point}
    (facts : CanonicalHeightFacts source.2)
    (equal : List.ofFn (pointCoordinates ∘ source.2) =
      List.ofFn (pointCoordinates ∘ target.2)) : CanonicalHeightFacts target.2 := by
  have injective : Function.Injective (@pointCoordinates curve) :=
    (Option.map_injective Subtype.val_injective).comp curve.toAffine.nonsingularPointEquiv.injective
  have points : List.ofFn source.2 = List.ofFn target.2 :=
    List.map_injective_iff.mpr injective (by simpa only [List.map_ofFn] using equal)
  have same : source = target := List.ofFn_inj'.mp points
  let index (i : Fin target.1) : Fin source.1 := i.cast (congrArg Sigma.fst same.symm)
  refine
    { reported := fun i => facts.reported (index i)
      error := fun i => facts.error (index i)
      error_nonneg := fun i => facts.error_nonneg (index i)
      within_error := fun i => ?_ }
  have matchPoint : source.2 (index i) = target.2 i := by
    cases same
    rfl
  exact matchPoint ▸ facts.within_error (index i)

end VerifiedLcalc
