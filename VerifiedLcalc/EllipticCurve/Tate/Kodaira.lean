/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic
public import VerifiedLcalc.EllipticCurve.Tate.LocalReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve

/-! # Canonical Kodaira symbols at rational primes

The PARI code specifies an exact canonical Tate symbol in the multiplicative
family, which includes good reduction as `I₀`. At an additive prime the
supported conclusion excludes this family.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

/-- The index of `Iₙ` in the PARI encoding. Code 1 represents `I₀`;
code `n + 4` represents `Iₙ` for positive `n`. -/
def kodairaIIndex (code : Int) : Option Nat :=
  if code = 1 then some 0
  else if 5 ≤ code then some (code - 4).toNat
  else none

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
    exact (multiplicity_dvd_iff_le hnabs).mpr le_rfl
  have hnext : ¬ (p : Int) ^ (n + 1) ∣ e.Δ := by
    rw [← Nat.cast_pow, Int.natCast_dvd]
    exact pow_succ_multiplicity_not_dvd hnabs
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

/-- The canonical Tate symbol is the claimed `Iₙ`, or lies outside that family
when the claim is additive. -/
def KodairaCodeSpec (W : WeierstrassCurve ℚ) [W.IsElliptic] (p : Nat) [Fact p.Prime]
    (code : Int) : Prop :=
  match kodairaIIndex code with
  | some n => W.reductionSymbol (RationalLocalRing p) = .I n
  | none => ∀ n, W.reductionSymbol (RationalLocalRing p) ≠ .I n

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
  · rw [if_pos hadd] at hf
    rw [hf]
    exact (W.forall_reductionSymbol_ne_I_iff R).mpr (ha.mpr hadd)
  · rw [if_neg hadd] at hf
    rw [hf]
    exact (W.reductionSymbol_eq_I_iff R _).mpr
      ⟨fun hAdd => hadd (ha.mp hAdd), discriminantValuation_eq e p hn⟩

end VerifiedLcalc.EllipticCurve
