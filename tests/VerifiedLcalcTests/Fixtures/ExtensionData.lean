/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import VerifiedLcalc.EllipticCurve.TwoFactorTorsion
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Ring.Fin
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Splitting
import TauCeti.Algebra.Polynomial.XPow.SubC
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion

/-! # Full torsion growth for 64.a4 over ℚ(i)

The [LMFDB JSON snapshot](https://www.lmfdb.org/EllipticCurve/Q/data/64.a4?_format=json)
has timestamp `2026-11-26T02:37:51.869443` and SHA-256
`04f6adcf757ac2ef6f7717b81c2d6d821d5d13f9be0e4de19aed02c852c5f454`.
It pairs the equation `[0, 0, 0, 1, 0]` with torsion growth row 2263, field
`[1, 0, 1]` of degree two, and factors `[2, 2]`.

The point `(i, 0)` certifies strict growth since a rational preimage would give
a rational square root of `-1`. Good reduction at the prime `(2 - i)` gives
an exact torsion divisor bound of four. The points `(i, 0)` and `(0, 0)` have
order two and generate the full torsion subgroup.
-/

@[expose] public section

namespace ExtensionDataFixture

open Polynomial WeierstrassCurve VerifiedLcalc

/-- The polynomial in the submitted quadratic row. -/
abbrev f : ℚ[X] := (TorsionGrowthFieldClaim.mk [1, 0, 1] 2).polynomial
private theorem f_eq : f = X ^ 2 + 1 := by
  ext n
  by_cases h : n < 3
  · interval_cases n <;> simp [f, TorsionGrowthFieldClaim.polynomial, coeff_X_pow, coeff_one]
  · have hn : 3 ≤ n := by omega
    have h₂ : n ≠ 2 := by omega
    have h₀ : n ≠ 0 := by omega
    simp [f, TorsionGrowthFieldClaim.polynomial, ofFn_coeff_eq_zero_of_ge _ hn,
      coeff_X_pow, coeff_one, h₂, h₀]
/-- The quadratic field in the submitted row. -/
abbrev K := AdjoinRoot f
/-- The submitted polynomial is irreducible over ℚ. -/
theorem f_irreducible : Irreducible f := f_eq ▸ Polynomial.irreducible_X_sq_add_one ℚ
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
/-- The integral Weierstrass model with Cremona label 64a4. -/
abbrev growthModel : WeierstrassCurve ℤ := ⟨0, 0, 0, 1, 0⟩
/-- The image of the polynomial variable. -/
noncomputable abbrev i : K := AdjoinRoot.root f
private theorem i_squared : i ^ 2 + 1 = 0 := by
  have e := congrArg (fun p => Polynomial.eval₂ (AdjoinRoot.of f) i p) f_eq
  rw [AdjoinRoot.eval₂_root] at e
  simpa using e.symm

noncomputable local instance : DecidableEq K := Classical.decEq _
private theorem onCurve : (growthModel.baseChange K).toAffine.Nonsingular i 0 := by
  have hΔ : growthModel.Δ = -64 := by decide +kernel
  apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero (by
    norm_num [baseChange, map_Δ, hΔ]) ).mp
  rw [Affine.equation_iff]
  simp [baseChange, growthModel]
  linear_combination -i * i_squared
private noncomputable def extraPoint : (growthModel.baseChange K).toAffine.Point :=
  .some i 0 onCurve
private theorem extraPoint_double : extraPoint + extraPoint = 0 := by
  apply (Affine.Point.some_add_self_eq_zero_iff onCurve).mpr
  simp [Affine.evalEval_polynomialY, baseChange, growthModel]

private theorem extraPoint_new : ∀ P : (growthModel.baseChange ℚ).toAffine.Point,
    Affine.Point.map (Algebra.ofId ℚ K) P ≠ extraPoint := by
  rintro (_ | ⟨x, y, h⟩) heq
  · contradiction
  · rw [Affine.Point.map_some] at heq
    have hx := (Affine.Point.some.inj heq).1
    change algebraMap ℚ K x = i at hx
    have hn := i_squared
    rw [← hx] at hn
    have hr : x ^ 2 + 1 = 0 := (algebraMap ℚ K).injective (by simpa using hn)
    nlinarith [sq_nonneg x]

/-- A point of order two outside the image of rational base change. -/
def growthEvidence : TorsionGrowthFieldFact growthModel where
  polynomial := f
  irreducible := f_irreducible
  growth := by
    refine ⟨extraPoint, isOfFinAddOrder_iff_nsmul_eq_zero.mpr ?_, extraPoint_new⟩
    exact ⟨2, by decide, by simpa only [two_nsmul] using extraPoint_double⟩

local instance : (growthModel.baseChange ℚ).IsElliptic :=
  ⟨by norm_num [growthModel, baseChange, map_Δ, Δ, b₂, b₄, b₆, b₈]⟩

certify_ec Growth64 from_json_string
  r#"{"ainvs":[0,0,0,1,0],"degree":4,"torsion":2,
    "torsion_growth":{"degree":2,"field":[1,0,1],"torsion":[2,2],"lmfdb_label":"64.a4"}}"#
  with_proofs ({ torsionGrowthField := some growthEvidence } : IntegralCurveProofs growthModel)

/-! # The torsion divisor bound from the split prime 5 -/

open IsDedekindDomain IsLocalRing
open scoped NumberField

private noncomputable def integralI : 𝓞 K :=
  ⟨i, ⟨X ^ 2 + 1, by
    simpa using (monic_X_pow_add_C (1 : ℤ) (by decide : 2 ≠ 0)),
    by simpa using i_squared⟩⟩

private theorem integralI_minpoly : minpoly ℤ integralI = X ^ 2 + 1 := by
  have hminQ : minpoly ℚ (integralI : K) = (minpoly ℤ integralI).map (Int.castRingHom ℚ) := by
    rw [← NumberField.RingOfIntegers.minpoly_coe,
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ integralI.isIntegral_coe, algebraMap_int_eq]
  have hmonic : f.Monic := by
    rw [f_eq]
    simpa using (monic_X_pow_add_C (1 : ℚ) (by decide : 2 ≠ 0))
  have hf : minpoly ℚ (integralI : K) = f := by
    refine (minpoly.eq_of_irreducible_of_monic f_irreducible ?_ hmonic).symm
    refine (congrArg (fun p : ℚ[X] => aeval (integralI : K) p) f_eq).trans ?_
    have hi : (integralI : K) ^ 2 + 1 = 0 := by
      change i ^ 2 + 1 = 0
      exact i_squared
    simpa using hi
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← hminQ, hf, f_eq]
  simp

private theorem integralI_generates : Algebra.adjoin ℚ {(integralI : K)} = ⊤ :=
  AdjoinRoot.adjoinRoot_eq_top

private noncomputable def fiveIdeal : Ideal (𝓞 K) := Ideal.span {2 - integralI}

private theorem fiveIdeal_norm : fiveIdeal.absNorm = 5 :=
  TauCeti.NumberField.GaussianRationals.absNorm_span_two_sub integralI_minpoly integralI_generates

private noncomputable def fivePlace : HeightOneSpectrum (𝓞 K) where
  asIdeal := fiveIdeal
  isPrime := Ideal.isPrime_of_irreducible_absNorm
    (fiveIdeal_norm ▸ (Nat.irreducible_iff_nat_prime 5).mpr Nat.prime_five)
  ne_bot := by
    intro bottom
    have hsize := fiveIdeal_norm
    rw [bottom, Ideal.absNorm_bot] at hsize
    omega

private theorem gaussianRank : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [NumberField.RingOfIntegers.rank]
  exact TauCeti.NumberField.GaussianRationals.finrank_eq_two integralI_minpoly integralI_generates

private theorem fivePlace_cast_mem_pow {q n : ℕ} (h : (q : 𝓞 K) ∈ fivePlace.asIdeal ^ n) :
    5 ^ n ∣ q ^ 2 := by
  have hnorm := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h)
  simpa only [map_pow, fivePlace, fiveIdeal_norm, Ideal.absNorm_span_natCast, gaussianRank]
    using hnorm

private theorem fivePlace_smallRamification (q : ℕ) (hq : q.Prime) :
    (q : 𝓞 K) ∉ fivePlace.asIdeal ^ (q - 1) := by
  intro mem
  have h := fivePlace_cast_mem_pow mem
  have hpos : q - 1 ≠ 0 := by
    have := hq.two_le
    omega
  have hdvd : 5 ∣ q ^ 2 := (dvd_pow_self 5 hpos).trans h
  have hs : 5 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hq).mp
    (Nat.prime_five.dvd_of_dvd_pow hdvd)
  subst q
  exact (by decide : ¬ (5 : ℕ) ^ (5 - 1) ∣ 5 ^ 2) h

private noncomputable abbrev fiveIntegers := (fivePlace.valuation K).valuationSubring

private noncomputable local instance : Algebra (𝓞 K) fiveIntegers :=
  ((algebraMap (𝓞 K) K).codRestrict fiveIntegers.toSubring fun r =>
    fivePlace.valuation_le_one r).toAlgebra

private local instance : IsScalarTower (𝓞 K) fiveIntegers K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private noncomputable def fiveResidueEquiv : ZMod 5 ≃+* ResidueField fiveIntegers := by
  classical
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdeal fivePlace.asIdeal fiveIntegers).toRingEquiv
  have hc : Nat.card (ResidueField fiveIntegers) = 5 :=
    (Nat.card_congr e.toEquiv).symm.trans
      ((Ideal.absNorm_eq_natCard fiveIdeal).symm.trans fiveIdeal_norm)
  let : Finite (ResidueField fiveIntegers) := (Nat.finite_of_card_ne_zero (by rw [hc]; decide))
  let : Fintype (ResidueField fiveIntegers) := Fintype.ofFinite _
  exact ZMod.ringEquivOfPrime _ Nat.prime_five (Nat.card_eq_fintype_card.symm.trans hc)

private noncomputable abbrev gaussianModel := growthModel.baseChange (𝓞 K)

private theorem gaussianModel_good : gaussianModel.Δ ∉ fivePlace.asIdeal := by
  intro mem
  have hΔ : gaussianModel.Δ = -(64 : 𝓞 K) := by
    norm_num [gaussianModel, growthModel, baseChange, map_Δ, Δ, b₂, b₄, b₆, b₈]
  rw [hΔ] at mem
  have hm : (64 : 𝓞 K) ∈ fivePlace.asIdeal ^ 1 := by
    simpa using (fivePlace.asIdeal.neg_mem mem)
  exact (by decide : ¬ (5 : ℕ) ^ 1 ∣ 64 ^ 2) (fivePlace_cast_mem_pow hm)

private theorem gaussianReduction_eq :
    (integralModel fiveIntegers (gaussianModel.baseChange K)).map (residue fiveIntegers) =
      (growthModel.baseChange (ZMod 5)).map fiveResidueEquiv.toRingHom := by
  rw [integralModel_baseChange_eq_map]
  unfold gaussianModel baseChange
  simp only [WeierstrassCurve.map_map]
  congr 1
  exact RingHom.ext_int _ _

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem gaussianReduction_card :
    Nat.card ((growthModel.baseChange (ZMod 5)).map fiveResidueEquiv.toRingHom).toAffine.Point =
      4 := by
  classical
  let W := growthModel.baseChange (ZMod 5)
  have hnonsingular : W.IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    change (growthModel.baseChange (ZMod 5)).Δ ≠ 0
    decide +kernel
  have hc : Nat.card W.toAffine.Point = 4 := by
    rw [← pointCount_eq_card_point, ← VerifiedLcalc.EllipticCurve.computePointCount_correct]
    decide +kernel
  refine ((Nat.card_congr (W.map fiveResidueEquiv.toRingHom).toAffine.nonsingularPointEquiv).trans
    ?_).trans hc
  rw [Nat.card_congr W.toAffine.nonsingularPointEquiv]
  -- Transport finite point counts as in Tau Ceti's `card_point_reduction_baseChange`.
  exact (Nat.card_congr
    ((fiveResidueEquiv.toEquiv.prodCongr fiveResidueEquiv.toEquiv).subtypeEquiv fun xy =>
      (Affine.map_nonsingular _ fiveResidueEquiv.injective xy.1 xy.2).symm).optionCongr).symm

private theorem gaussianTorsion_dvd_four :
    Nat.card (AddCommGroup.torsion (growthModel.baseChange K).toAffine.Point) ∣ 4 := by
  let := gaussianModel.isElliptic_integralModel_baseChange (K := K) fivePlace gaussianModel_good
  have h := Affine.Point.card_torsion_dvd_card_reduction
    (W := (gaussianModel.baseChange K).toAffine) fivePlace fivePlace_smallRamification
  change Nat.card (AddCommGroup.torsion (gaussianModel.baseChange K).toAffine.Point) ∣
    Nat.card ((integralModel fiveIntegers (gaussianModel.baseChange K)).map
      (residue fiveIntegers)).toAffine.Point at h
  rw [gaussianReduction_eq, gaussianReduction_card] at h
  have heq : gaussianModel.baseChange K = growthModel.baseChange K := by
    unfold gaussianModel baseChange
    rw [WeierstrassCurve.map_map]
    congr 1
  exact (congrArg (fun W : WeierstrassCurve K =>
    Nat.card (AddCommGroup.torsion W.toAffine.Point) ∣ 4) heq).mp h

private theorem origin_on_curve : (growthModel.baseChange K).toAffine.Nonsingular 0 0 := by
  have hΔ : growthModel.Δ = -64 := by decide +kernel
  apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero (by norm_num [baseChange, map_Δ, hΔ])).mp
  simp [Affine.equation_iff, baseChange, growthModel]

private noncomputable def originTwo : (growthModel.baseChange K).toAffine.Point :=
  .some 0 0 origin_on_curve

private theorem originTwo_order : addOrderOf originTwo = 2 := by
  have h : originTwo + originTwo = 0 := by
    apply (Affine.Point.some_add_self_eq_zero_iff origin_on_curve).mpr
    simp [Affine.evalEval_polynomialY, baseChange, growthModel]
  exact addOrderOf_eq_prime (by simpa only [two_nsmul] using h)
    (Affine.Point.some_ne_zero origin_on_curve)

private theorem extraPoint_order : addOrderOf extraPoint = 2 :=
  addOrderOf_eq_prime (by simpa only [two_nsmul] using extraPoint_double)
    (Affine.Point.some_ne_zero onCurve)

private theorem extraPoint_independent : extraPoint ∉ AddSubgroup.zmultiples originTwo := by
  intro mem
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp mem
  have hr : (m % 2) • originTwo = extraPoint := by
    simpa only [originTwo_order, Nat.cast_ofNat] using (mod_addOrderOf_zsmul originTwo m).trans hm
  have hcases : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hcases with h | h
  · rw [h, zero_zsmul] at hr
    exact Affine.Point.some_ne_zero onCurve hr.symm
  · rw [h, one_zsmul] at hr
    have hi : (0 : K) = i := (Affine.Point.some.inj hr).1
    have bad := i_squared
    rw [← hi] at bad
    norm_num at bad

/-- The full torsion of 64.a4 over `ℚ(i)` is an elementary abelian group of rank two. -/
theorem gaussianTorsion :
    Nonempty ((Fin 2 → ZMod 2) ≃+
      AddCommGroup.torsion (growthModel.baseChange K).toAffine.Point) := by
  obtain ⟨e, -, -⟩ := VerifiedLcalc.EllipticCurve.exists_torsion_addEquiv_two_factor
    (n := 2) (by decide) extraPoint_order originTwo_order extraPoint_independent
    gaussianTorsion_dvd_four
  exact ⟨(RingEquiv.piFinTwo (fun _ : Fin 2 => ZMod 2)).toAddEquiv.trans e⟩

/-- The full row proof for the quadratic growth of 64.a4. -/
noncomputable def fullEvidence : TorsionGrowthFacts growthModel where
  toTorsionGrowthFieldFact := growthEvidence
  elliptic := ⟨by
    change IsUnit (growthModel.baseChange K).Δ
    exact isUnit_iff_ne_zero.mpr (by
      norm_num [growthModel, baseChange, map_Δ, Δ, b₂, b₄, b₆, b₈])⟩
  factorCount := 2
  factor := fun _ => 2
  factors_nontrivial := fun _ => le_rfl
  factors_divide := fun _ _ _ => dvd_rfl
  equivalence := Classical.choice gaussianTorsion

noncomputable section

certify_ec FullGrowth64 from_json_string
  r#"{"ainvs":[0,0,0,1,0],"degree":4,"torsion":2,"discriminant":-64,
    "torsion_growth":{"degree":2,"field":[1,0,1],"torsion":[2,2],"lmfdb_label":"64.a4"}}"#
  with_proofs ({ torsionGrowth := some fullEvidence } : IntegralCurveProofs growthModel)

end

end ExtensionDataFixture
