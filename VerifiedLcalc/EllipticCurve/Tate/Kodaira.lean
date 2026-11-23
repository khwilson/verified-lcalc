/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic
public import VerifiedLcalc.EllipticCurve.Tate.LocalReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
public import VerifiedLcalc.EllipticCurve.Tate.KodairaSpecs

/-! # Canonical Kodaira symbols at rational primes

The PARI code specifies an exact canonical Tate symbol in the multiplicative
family, which includes good reduction as `I₀`. At an additive prime the
supported conclusion excludes this family.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

/-- Verify that a PARI code belongs to the right family, and its index when
the reduction is good or multiplicative. Zero is not a valid PARI code. -/
def checkKodairaCode (e : WeierstrassCurve ℤ) (p : Nat) (code : Int) : Bool :=
  (code != 0) && (kodairaIIndex code ==
    if modelReduction e p = .additive then none else some (padicValNat p e.Δ.natAbs))

private theorem discriminantValuation_eq (e : WeierstrassCurve ℤ) (p : Nat)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    [IsMinimal (RationalLocalRing p) (e.baseChange ℚ)] (hn : e.Δ ≠ 0) :
    (e.baseChange ℚ).localMinimalDiscriminantValuation (RationalLocalRing p) =
      padicValNat p e.Δ.natAbs := by
  let v := rationalPlace p
  let W := e.baseChange ℚ
  let R := RationalLocalRing p
  let n := padicValNat p e.Δ.natAbs
  have hnabs := Int.natAbs_ne_zero.mpr hn
  have hdiv : (p : Int) ^ n ∣ e.Δ := by
    rw [← Nat.cast_pow, Int.natCast_dvd]
    exact (multiplicity_dvd_iff_le hnabs).mpr (by simp only [n, Nat.padicValNat_def, le_refl])
  have hnext : ¬ (p : Int) ^ (n + 1) ∣ e.Δ := by
    rw [← Nat.cast_pow, Int.natCast_dvd]
    simpa only [n, Nat.padicValNat_def] using (pow_succ_multiplicity_not_dvd (p := p) hnabs)
  have hv := completion_intCast_valuation_eq p n e.Δ hdiv hnext
  rw [completion_intCast_valuation] at hv
  have hvaluation := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul R 1 (one_smul _ _)
  have hΔ : W.Δ = (e.Δ : ℚ) := by
    simp only [W, WeierstrassCurve.baseChange, map_Δ, eq_intCast]
  have hvcast : v.valuation ℚ (e.Δ : ℚ) = v.intValuation (e.Δ : NumberField.RingOfIntegers ℚ) := by
    simpa only [map_intCast] using v.valuation_of_algebraMap (K := ℚ)
      (e.Δ : NumberField.RingOfIntegers ℚ)
  rw [hΔ, v.valuation_maximalIdeal_localizationAtPrime, hvcast] at hvaluation
  exact_mod_cast neg_injective (WithZero.exp_injective (hvaluation.symm.trans hv))

/-- The checked code identifies the strongest currently certified statement
about the canonical Tate symbol of the supplied locally minimal equation. -/
theorem checkKodairaCode_correct (e : WeierstrassCurve ℤ) (p : Nat) [Fact p.Prime]
    [(e.baseChange ℚ).IsElliptic] [IsMinimal (RationalLocalRing p) (e.baseChange ℚ)]
    (hn : e.Δ ≠ 0) (code : Int) (h : checkKodairaCode e p code = true) :
    KodairaCodeSpec (e.baseChange ℚ) p code := by
  let W := e.baseChange ℚ
  let R := RationalLocalRing p
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  have ha : (W.minimal R).HasAdditiveReduction R ↔ modelReduction e p = .additive := by
    rw [hasAdditiveReduction_iff_of_isMinimal_smul R C hC, hasAdditiveReduction_at_iff,
      modelReduction_additive_iff]
    simp only [WeierstrassCurve.baseChange, map_Δ, map_c₄, eq_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf := (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2)
  unfold KodairaCodeSpec
  by_cases hadd : modelReduction e p = .additive
  · rw [ite_eq_left hadd] at hf
    rw [hf]
    exact (W.forall_reductionSymbol_ne_I_iff (R := R)).mpr (ha.mpr hadd)
  · rw [ite_eq_right hadd] at hf
    rw [hf]
    exact (W.reductionSymbol_eq_I_iff (R := R) _).mpr
      ⟨fun hAdd => hadd (ha.mp hAdd), discriminantValuation_eq e p hn⟩

end VerifiedLcalc.EllipticCurve
