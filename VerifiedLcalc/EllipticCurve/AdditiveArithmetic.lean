module

public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import VerifiedLcalc.EllipticCurve.ReductionCore

@[expose] public section
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open scoped WithZero
namespace VerifiedLcalc.EllipticCurve

/-- Discreteness of the value group bounds a change-of-variables scale. -/
theorem scale_bound (a d : WithZero (Multiplicative ℤ)) (n : ℕ) (_hn : 0 < n)
    (hd : WithZero.exp (-(n : ℤ)) < d) (h : a ^ n * d ≤ 1) : a ≤ 1 := by
  by_contra ha
  have ha : 1 < a := lt_of_not_ge ha
  have ha0 : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
  have hz : 1 ≤ WithZero.log a := by
    have : WithZero.exp (0 : ℤ) < WithZero.exp (WithZero.log a) := by simpa only [WithZero.exp_zero, WithZero.exp_log ha0] using ha
    have := WithZero.exp_lt_exp.mp this
    omega
  have hea : WithZero.exp (1 : ℤ) ≤ a := by
    rw [← WithZero.exp_log ha0]
    exact WithZero.exp_le_exp.mpr hz
  have hpow : WithZero.exp (n : ℤ) ≤ a ^ n := by
    simpa only [← WithZero.exp_nsmul, nsmul_eq_mul, mul_one] using pow_le_pow_left₀ bot_le hea n
  have hmul : 1 < WithZero.exp (n : ℤ) * d := by
    have := mul_lt_mul_of_pos_left hd (show 0 < WithZero.exp (n : ℤ) from WithZero.exp_pos)
    simpa only [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero] using this
  exact (not_lt_of_ge h) (hmul.trans_le (mul_le_mul_of_nonneg_right hpow bot_le))

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral equation with discriminant valuation below twelve is minimal.
The valuation may be any normalized integer-valued valuation with integer ring R. -/
theorem minimal_of_small_discriminant (W : WeierstrassCurve K) [WeierstrassCurve.IsIntegral R W]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : v.Integers R)
    (hd : WithZero.exp (-12 : ℤ) < v W.Δ) : WeierstrassCurve.IsMinimal R W := by
  refine ⟨⟨by simpa using ‹WeierstrassCurve.IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe,
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W),
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : v (C • W).Δ ≤ 1 := by
    rw [← WeierstrassCurve.integralModel_Δ_eq R (C • W)]
    exact hv.map_le_one _
  rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow] at hint
  have hinv : v ((C.u : K)⁻¹) ≤ 1 := by
    exact scale_bound _ _ 12 (by decide) hd (by simpa only [Units.val_inv_eq_inv_val] using hint)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hinv
  have hrval : valuation K (maximalIdeal R) ((C.u : K)⁻¹) ≤ 1 := by
    rw [← hr]
    exact valuation_le_one _ _
  simpa [WeierstrassCurve.variableChange_Δ, map_mul, map_pow] using
    mul_le_of_le_one_left' (pow_le_one' hrval 12)
end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

theorem rationalPlace_intValuation_gt (p k : ℕ) [Fact p.Prime] (n : ℤ)
    (h : ¬ (p : ℤ) ^ k ∣ n) :
    WithZero.exp (-(k : ℤ)) < (rationalPlace p).intValuation (n : 𝓞 ℚ) := by
  rw [← not_le, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  intro hn
  have hm := Ideal.mem_map_of_mem Rat.ringOfIntegersEquiv.toRingHom hn
  have hi : (rationalPlace p).asIdeal.map Rat.ringOfIntegersEquiv.toRingHom =
      Ideal.span {(p : ℤ)} := by
    rw [← RationalPrimes.integerPlace_asIdeal]
    change ((HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv)
      ((HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).symm _)).asIdeal = _
    rw [Equiv.apply_symm_apply]
  rw [Ideal.map_pow, hi, Ideal.span_singleton_pow] at hm
  apply h
  exact Ideal.mem_span_singleton.mp (by simpa using hm)

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The completion valuation of an integer agrees with the ideal valuation. -/
theorem completion_intCast_valuation (p : ℕ) [Fact p.Prime] (n : ℤ) :
    Valued.v (n : (rationalPlace p).adicCompletion ℚ) =
      (rationalPlace p).intValuation (n : 𝓞 ℚ) := by
  let v := rationalPlace p
  have ht := HeightOneSpectrum.valuedAdicCompletion_eq_valuation
    (R := 𝓞 ℚ) (K := ℚ) v (n : 𝓞 ℚ)
  have ht' : Valued.v (n : v.adicCompletion ℚ) = v.valuation ℚ (n : ℚ) := by
    simpa only [map_intCast] using ht
  apply ht'.trans
  simpa only [map_intCast] using (v.valuation_of_algebraMap (K := ℚ) (n : 𝓞 ℚ))

/-- A divisibility witness gives the complementary bound on the ideal valuation. -/
theorem rationalPlace_intValuation_le (p k : ℕ) [Fact p.Prime] (n : ℤ)
    (h : (p : ℤ) ^ k ∣ n) :
    (rationalPlace p).intValuation (n : 𝓞 ℚ) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have hi : (rationalPlace p).asIdeal.map Rat.ringOfIntegersEquiv.toRingHom =
      Ideal.span {(p : ℤ)} := by
    rw [← RationalPrimes.integerPlace_asIdeal]
    change ((HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv)
      ((HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).symm _)).asIdeal = _
    rw [Equiv.apply_symm_apply]
  have hm : Rat.ringOfIntegersEquiv (n : 𝓞 ℚ) ∈
      ((rationalPlace p).asIdeal ^ k).map Rat.ringOfIntegersEquiv.toRingHom := by
    rw [Ideal.map_pow, hi, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (by simpa using h)
  obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective
    Rat.ringOfIntegersEquiv.toRingHom Rat.ringOfIntegersEquiv.surjective).mp hm
  have he' : x = (n : 𝓞 ℚ) := Rat.ringOfIntegersEquiv.injective he
  exact he' ▸ hx

/-- Exact normalized integer valuations from two finite divisibility checks. -/
theorem completion_intCast_valuation_eq (p k : ℕ) [Fact p.Prime] (n : ℤ)
    (h : (p : ℤ) ^ k ∣ n) (hnext : ¬ (p : ℤ) ^ (k + 1) ∣ n) :
    Valued.v (n : (rationalPlace p).adicCompletion ℚ) = WithZero.exp (-(k : ℤ)) := by
  rw [completion_intCast_valuation]
  have hlo := rationalPlace_intValuation_gt p (k + 1) n hnext
  have hhi := rationalPlace_intValuation_le p k n h
  have hn : (rationalPlace p).intValuation (n : 𝓞 ℚ) ≠ 0 := by
    intro hz
    simp only [hz, not_lt_zero] at hlo
  rw [← WithZero.exp_log hn] at hlo hhi ⊢
  have hlo' := WithZero.exp_lt_exp.mp hlo
  have hhi' := WithZero.exp_le_exp.mp hhi
  congr 1
  push_cast at hlo'
  omega

theorem minimal_at_of_discriminant_not_dvd (e : Artifacts.CurveEquation)
    (p : ℕ) [Fact p.Prime] (h : ¬ (p : ℤ) ^ 12 ∣ discriminant e) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((weierstrass e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  let v := rationalPlace p
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := (weierstrass e R).baseChange K
  let : WeierstrassCurve.IsIntegral R W := ⟨⟨weierstrass e R, rfl⟩⟩
  apply minimal_of_small_discriminant W Valued.v
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
  have heq : W.Δ = algebraMap (𝓞 ℚ) K (discriminant e : 𝓞 ℚ) := by
    simp only [W, WeierstrassCurve.baseChange, weierstrass_map,
      weierstrass_discriminant, map_intCast]
  rw [heq, map_intCast, completion_intCast_valuation]
  exact rationalPlace_intValuation_gt p 12 (discriminant e) h

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The executable c4 invariant is mathlib's invariant. -/
theorem modelC4_correct (e : Artifacts.CurveEquation) :
    modelC4 e = (weierstrass e ℤ).c₄ := rfl

/-- Exact specification of the sufficient local minimality test. -/
theorem discriminantMinimalAt_correct (e : Artifacts.CurveEquation) (p : ℕ) :
    discriminantMinimalAt e p = true ↔ ¬ (p : ℤ) ^ 12 ∣ discriminant e := by
  simp only [discriminantMinimalAt, decide_eq_true_eq, ne_eq, Int.dvd_iff_emod_eq_zero]

/-- The additive branch classifies the supplied singular cubic by its two
invariants. It becomes a statement about the elliptic curve once minimality is proved. -/
theorem modelReduction_additive_iff (e : Artifacts.CurveEquation) (p : ℕ) :
    modelReduction e p = .additive ↔
      (weierstrass e (ZMod p)).Δ = 0 ∧ (weierstrass e (ZMod p)).c₄ = 0 := by
  rw [weierstrass_discriminant, weierstrass_c4, ← modelC4_correct]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  by_cases hd : discriminant e % (p : ℤ) = 0 <;>
    by_cases hc : modelC4 e % (p : ℤ) = 0 <;>
    simp [modelReduction, hd, hc]

/-- The good branch is exactly smooth reduction of the supplied equation. -/
theorem modelReduction_good_iff (e : Artifacts.CurveEquation) (p : ℕ) :
    modelReduction e p = .good ↔ (weierstrass e (ZMod p)).Δ ≠ 0 := by
  rw [← goodReduction_correct]
  by_cases hd : discriminant e % (p : ℤ) = 0 <;>
    by_cases hc : modelC4 e % (p : ℤ) = 0 <;>
    simp [modelReduction, goodReduction, hd, hc]

/-- The multiplicative branch is a nodal cubic: Delta vanishes and c4 does not. -/
theorem modelReduction_multiplicative_iff (e : Artifacts.CurveEquation) (p : ℕ) :
    modelReduction e p = .multiplicative ↔
      (weierstrass e (ZMod p)).Δ = 0 ∧ (weierstrass e (ZMod p)).c₄ ≠ 0 := by
  rw [weierstrass_discriminant, weierstrass_c4, ← modelC4_correct]
  simp only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  by_cases hd : discriminant e % (p : ℤ) = 0 <;>
    by_cases hc : modelC4 e % (p : ℤ) = 0 <;>
    simp [modelReduction, hd, hc]

/-- Additive reduction has zero trace, including in characteristics two and three. -/
theorem additive_trace_zero (e : Artifacts.CurveEquation) (p : ℕ) [Fact p.Prime]
    (ha : modelReduction e p = .additive) : frobeniusTrace e p = 0 := by
  obtain ⟨hΔ, hc⟩ := (modelReduction_additive_iff e p).mp ha
  rw [frobeniusTrace_eq_tauceti]
  exact WeierstrassCurve.frobeniusTrace_eq_zero_of_c₄_eq_zero _ hΔ hc

/-- At an additive prime of a minimal input equation the actual local Euler
polynomial is one. This is an exact equality, not a zero tolerance. -/
theorem additive_localPolynomial (e : Artifacts.CurveEquation)
    (hn : discriminant e ≠ 0) (p : ℕ) [Fact p.Prime]
    (hmin : WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((weierstrass e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)))
    (ha : modelReduction e p = .additive) :
    ((weierstrass e ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPlace p).adicCompletionIntegers ℚ) = 1 := by
  rw [minimal_localPolynomial e hn p hmin]
  have ht := additive_trace_zero e p ha
  have hg : goodReduction e p = false := by
    have hd := (modelReduction_additive_iff e p).mp ha |>.1
    cases h : goodReduction e p
    · rfl
    · exact False.elim ((goodReduction_correct e p).mp h hd)
  simp [modelFactor, ht, hg]

end VerifiedLcalc.EllipticCurve
