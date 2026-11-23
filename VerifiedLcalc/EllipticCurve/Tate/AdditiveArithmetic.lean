/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.UpstreamCandidates.TauCeti.Minimality
public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import VerifiedLcalc.EllipticCurve.ReductionCore

/-! # Mathematical facts used by local additive reduction proofs -/

@[expose] public section
open WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open scoped WithZero

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
    rw [← Int.ideal_span_absNorm_eq_self
      (RationalPrimes.integerPlace (rationalPlace p)).asIdeal,
      RationalPrimes.norm_integerPlace, rationalPlace_norm]
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
    rw [← Int.ideal_span_absNorm_eq_self
      (RationalPrimes.integerPlace (rationalPlace p)).asIdeal,
      RationalPrimes.norm_integerPlace, rationalPlace_norm]
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

theorem minimal_at_of_discriminant_not_dvd (e : (WeierstrassCurve ℤ))
    (p : ℕ) [Fact p.Prime] (h : ¬ (p : ℤ) ^ 12 ∣ e.Δ) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  let v := rationalPlace p
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := (WeierstrassCurve.baseChange e R).baseChange K
  let : WeierstrassCurve.IsIntegral R W := ⟨⟨WeierstrassCurve.baseChange e R, rfl⟩⟩
  apply minimal_of_small_discriminant W Valued.v
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
  have heq : W.Δ = algebraMap (𝓞 ℚ) K (e.Δ : 𝓞 ℚ) := by
    simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast, map_intCast]
  rw [heq, map_intCast, completion_intCast_valuation]
  exact rationalPlace_intValuation_gt p 12 (e.Δ) h

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- Exact specification of the sufficient local minimality test. -/
theorem discriminantMinimalAt_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) :
    discriminantMinimalAt e p = true ↔ ¬ (p : ℤ) ^ 12 ∣ e.Δ := by
  simp only [discriminantMinimalAt, decide_eq_true_eq, ne_eq, Int.dvd_iff_emod_eq_zero]

/-- The additive branch classifies the supplied singular cubic by its two
invariants. It becomes a statement about the elliptic curve once minimality is proved. -/
theorem modelReduction_additive_iff (e : (WeierstrassCurve ℤ)) (p : ℕ) :
    modelReduction e p = .additive ↔
      (WeierstrassCurve.baseChange e (ZMod p)).Δ = 0 ∧
      (WeierstrassCurve.baseChange e (ZMod p)).c₄ = 0 := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ,
    WeierstrassCurve.map_c₄, eq_intCast]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  by_cases hd : e.Δ % (p : ℤ) = 0 <;>
    by_cases hc : e.c₄ % (p : ℤ) = 0 <;>
    simp [modelReduction, hd, hc]

/-- The good branch is exactly smooth reduction of the supplied equation. -/
theorem modelReduction_good_iff (e : (WeierstrassCurve ℤ)) (p : ℕ) :
    modelReduction e p = .good ↔ (WeierstrassCurve.baseChange e (ZMod p)).Δ ≠ 0 := by
  rw [← goodReduction_correct]
  by_cases hd : e.Δ % (p : ℤ) = 0 <;>
    by_cases hc : e.c₄ % (p : ℤ) = 0 <;>
    simp [modelReduction, goodReduction, hd, hc]

/-- The multiplicative branch is a nodal cubic: Delta vanishes and c4 does not. -/
theorem modelReduction_multiplicative_iff (e : (WeierstrassCurve ℤ)) (p : ℕ) :
    modelReduction e p = .multiplicative ↔
      (WeierstrassCurve.baseChange e (ZMod p)).Δ = 0 ∧
      (WeierstrassCurve.baseChange e (ZMod p)).c₄ ≠ 0 := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ,
    WeierstrassCurve.map_c₄, eq_intCast]
  simp only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  by_cases hd : e.Δ % (p : ℤ) = 0 <;>
    by_cases hc : e.c₄ % (p : ℤ) = 0 <;>
    simp [modelReduction, hd, hc]

/-- Additive reduction has zero trace, including in characteristics two and three. -/
theorem additive_trace_zero (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (ha : modelReduction e p = .additive) : computeFrobeniusTrace e p = 0 := by
  obtain ⟨hΔ, hc⟩ := (modelReduction_additive_iff e p).mp ha
  rw [computeFrobeniusTrace_correct]
  exact WeierstrassCurve.frobeniusTrace_eq_zero_of_c₄_eq_zero _ hΔ hc

/-- At an additive prime of a minimal input equation the actual local Euler
polynomial is one. This is an exact equality, not a zero tolerance. -/
theorem additive_localPolynomial (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (p : ℕ) [Fact p.Prime]
    (hmin : WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)))
    (ha : modelReduction e p = .additive) :
    ((WeierstrassCurve.baseChange e ℚ).baseChange
      ((rationalPlace p).adicCompletion ℚ)).localPolynomial
        ((rationalPlace p).adicCompletionIntegers ℚ) = 1 := by
  rw [minimal_localPolynomial e hn p hmin]
  have ht := additive_trace_zero e p ha
  have hg : goodReduction e p = false := by
    have hd := (modelReduction_additive_iff e p).mp ha |>.1
    cases h : goodReduction e p
    · rfl
    · exact False.elim ((goodReduction_correct e p).mp h hd)
  simp [ht, hg]

end VerifiedLcalc.EllipticCurve
