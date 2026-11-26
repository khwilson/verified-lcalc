/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic
public import VerifiedLcalc.EllipticCurve.Tate.LocalReduction
public import VerifiedLcalc.EllipticCurve.Tate.TamagawaSpecs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.LocalIndex
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-! # Intrinsic Tamagawa numbers of rational curves

Good reduction and multiplicative reduction of index one both give the
intrinsic Tamagawa number one over the completed field.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

open WeierstrassCurve NumberField IsDedekindDomain
open scoped WithZero

/-- At a rational prime, an integer prime to the residue characteristic
has normalized valuation one in the completion. -/
private theorem completion_valuation_of_not_dvd (p : ℕ) [Fact p.Prime] (n : ℤ)
    (h : ¬ (p : ℤ) ∣ n) :
    Valued.v (n : (rationalPlace p).adicCompletion ℚ) = 1 := by
  simpa using completion_intCast_valuation_eq p 0 n (by simp) (by simpa using h)

section Place

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]

private theorem completedIntegral (e : WeierstrassCurve ℤ) (v : HeightOneSpectrum R) :
    ((e.baseChange ℚ).baseChange (v.adicCompletion ℚ)).IsIntegral
      (v.adicCompletionIntegers ℚ) := by
  refine ⟨⟨e.baseChange _, ?_⟩⟩
  ext <;> simp [WeierstrassCurve.baseChange]

variable [Ring.HasFiniteQuotients R]

private theorem tamagawaNumberAt_adicValued (e : WeierstrassCurve ℤ)
    (v : HeightOneSpectrum R) :
    (e.baseChange ℚ).tamagawaNumberAt v =
      ((e.baseChange ℚ).baseChange (v.adicCompletion ℚ)).tamagawaNumber
        (Valued.v : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ))) := by
  let F := v.adicCompletion ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let W := (e.baseChange ℚ).baseChange F
  rw [tamagawaNumberAt_def]
  convert W.tamagawaNumber_congr (ValuativeRel.valuation F)
    (ValuativeRel.isEquiv (ValuativeRel.valuation F) V) using 2
  dsimp only [W, WeierstrassCurve.baseChange]
  exact congrArg (fun f : ℚ →+* F => (e.baseChange ℚ).map f) (Subsingleton.elim _ _)

/-- Unit discriminant of the integral model gives Tamagawa factor one. -/
theorem tamagawaNumberAt_eq_one_of_unit_discriminant (e : WeierstrassCurve ℤ)
    (v : HeightOneSpectrum R)
    (h : Valued.v (e.Δ : v.adicCompletion ℚ) = 1) :
    (e.baseChange ℚ).tamagawaNumberAt v = 1 := by
  let F := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let W := (e.baseChange ℚ).baseChange F
  let := completedIntegral e v
  have hΔ : W.Δ = (e.Δ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_Δ, eq_intCast, map_intCast]
  have hv : (IsDiscreteValuationRing.maximalIdeal S).valuation _ W.Δ = 1 := by
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, h]
  let : W.IsMinimal V.valuationSubring := isMinimal_of_valuation_Δ_eq_one S W hv
  let : W.HasGoodReduction V.valuationSubring := ⟨hv⟩
  rw [tamagawaNumberAt_adicValued]
  exact W.tamagawaNumber_eq_one_of_hasGoodReduction V

local instance (v : HeightOneSpectrum R) : Finite (R ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

private theorem completedSymbol_eq_I_one (e : WeierstrassCurve ℤ) (v : HeightOneSpectrum R)
    [(e.baseChange ℚ).IsElliptic]
    (hd : Valued.v (e.Δ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hc : Valued.v (e.c₄ : v.adicCompletion ℚ) = 1) :
    ((e.baseChange ℚ).baseChange (v.adicCompletion ℚ)).reductionSymbol
      (v.adicCompletionIntegers ℚ) = .I 1 := by
  let F := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  let W := (e.baseChange ℚ).baseChange F
  let := completedIntegral e v
  have hΔ : W.Δ = (e.Δ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_Δ, eq_intCast, map_intCast]
  have hc₄ : W.c₄ = (e.c₄ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_c₄, eq_intCast, map_intCast]
  have hcval : (IsDiscreteValuationRing.maximalIdeal S).valuation _ W.c₄ = 1 := by
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hc₄, hc]
  let := isMinimal_of_valuation_c₄_eq_one S W hcval
  have hmul : W.HasMultiplicativeReduction S := by
    refine ⟨?_, hcval⟩
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, hd, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by decide)
  have hminval := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul S 1 (one_smul _ _)
  rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, hd] at hminval
  have hn : W.localMinimalDiscriminantValuation S = 1 := by
    exact_mod_cast neg_injective (WithZero.exp_injective hminval.symm)
  change W.reductionSymbol S = .I 1
  rw [W.reductionSymbol_eq_I_of_hasMultiplicativeReduction (R := S), hn]

/-- Discriminant valuation one and unit c₄ give Tamagawa factor one at the completed place. -/
theorem tamagawaNumberAt_eq_one_of_valuation_I_one (e : WeierstrassCurve ℤ)
    (v : HeightOneSpectrum R) [(e.baseChange ℚ).IsElliptic]
    (hd : Valued.v (e.Δ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hc : Valued.v (e.c₄ : v.adicCompletion ℚ) = 1) :
    (e.baseChange ℚ).tamagawaNumberAt v = 1 := by
  let F := v.adicCompletion ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let S := V.valuationSubring
  let W := (e.baseChange ℚ).baseChange F
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S :=
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := ℚ)).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  let : Finite (IsLocalRing.ResidueField S) := by
    change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
    infer_instance
  have hsymbol : W.reductionSymbol S = .I 1 := completedSymbol_eq_I_one e v hd hc
  obtain ⟨C, D, ϖ, _, hD, hϖ, hterminal⟩ := (W.reductionSymbol_eq_iff (R := S)).mp hsymbol
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  let : (C.baseChange F).IsElliptic := hD ▸ inferInstanceAs (D • W).IsElliptic
  have hlocal := (C.baseChange F).tamagawaNumber_eq_tateLocalIndex V hspan
    (by simpa only [integralModel_baseChange_self] using hterminal)
  rw [tamagawaNumberAt_adicValued]
  change W.tamagawaNumber V = 1
  rw [← W.tamagawaNumber_smul V D, hD, hlocal, integralModel_baseChange_self,
    tateLocalIndex_I_one]

end Place

/-- The intrinsic local Tamagawa number is one at a good prime of the
checked model. The point-group index is taken over the completion. -/
theorem tamagawaNumberAt_eq_one_of_good_prime (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] (hd : ¬ (p : ℤ) ∣ e.Δ) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 :=
  tamagawaNumberAt_eq_one_of_unit_discriminant e (rationalPlace p)
    (completion_valuation_of_not_dvd p e.Δ hd)

/-- At multiplicative reduction with discriminant valuation one, the
intrinsic Tamagawa number is one in both splitting cases. -/
theorem tamagawaNumberAt_eq_one_of_multiplicative_index_one (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (hd : (p : ℤ) ∣ e.Δ)
    (hd₂ : ¬ (p : ℤ) ^ 2 ∣ e.Δ) (hc : ¬ (p : ℤ) ∣ e.c₄) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 :=
  tamagawaNumberAt_eq_one_of_valuation_I_one e (rationalPlace p)
    (by simpa using completion_intCast_valuation_eq p 1 e.Δ (by simpa using hd) hd₂)
    (completion_valuation_of_not_dvd p e.c₄ hc)

/-- The finite support test implies that the intrinsic Tamagawa factor is one. -/
theorem supportsTamagawaOne_correct (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (h : supportsTamagawaOne e p = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 := by
  simp only [supportsTamagawaOne, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hd | ⟨hd, hd₂, hc⟩
  · exact tamagawaNumberAt_eq_one_of_good_prime e p hd
  · exact tamagawaNumberAt_eq_one_of_multiplicative_index_one e p hd hd₂ hc

set_option backward.isDefEq.respectTransparency.types false in
private theorem integerPlaceValuation_eq (v : HeightOneSpectrum ℤ) (p k : ℕ) (n : ℤ)
    (hp : v.asIdeal = Ideal.span {(p : ℤ)}) (h : (p : ℤ) ^ k ∣ n)
    (hnext : ¬ (p : ℤ) ^ (k + 1) ∣ n) :
    Valued.v (n : v.adicCompletion ℚ) = WithZero.exp (-(k : ℤ)) := by
  have hpow (j : ℕ) : v.intValuation n ≤ WithZero.exp (-(j : ℤ)) ↔ (p : ℤ) ^ j ∣ n := by
    rw [v.intValuation_le_pow_iff_mem, hp, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hlo : WithZero.exp (-((k + 1 : ℕ) : ℤ)) < v.intValuation n :=
    lt_of_not_ge fun ht => hnext ((hpow (k + 1)).mp ht)
  have hhi := (hpow k).mpr h
  have hne : v.intValuation n ≠ 0 := by
    intro hz
    rw [hz] at hlo
    exact not_lt_zero hlo
  have hv : Valued.v (n : v.adicCompletion ℚ) = v.intValuation n := by
    have he := v.valuedAdicCompletion_eq_valuation' (K := ℚ) (n : ℚ)
    have hf := v.valuation_of_algebraMap (K := ℚ) n
    change v.valuation ℚ (algebraMap ℤ ℚ n) = _ at hf
    have hi : algebraMap ℤ ℚ n = (n : ℚ) := by
      rw [algebraMap_int_eq]
      rfl
    rw [hi] at hf
    have hc := congrFun (v.algebraMap_adicCompletion (K := ℚ) (S := ℚ)) (n : ℚ)
    simp only [Function.comp_apply, Algebra.algebraMap_self_apply] at hc
    have hcast (f : ℚ →+* v.adicCompletion ℚ) : f (n : ℚ) = (n : v.adicCompletion ℚ) :=
      map_intCast f n
    rw [hcast] at hc
    exact (congrArg (fun x : v.adicCompletion ℚ => Valued.v x) hc).trans (he.trans hf)
  rw [hv, ← WithZero.exp_log hne]
  rw [← WithZero.exp_log hne] at hlo hhi
  have hlow := WithZero.exp_lt_exp.mp hlo
  have hhigh := WithZero.exp_le_exp.mp hhi
  congr 1
  omega


/-- The intrinsic Tamagawa product is one when an exhaustive discriminant-prime
list passes the good-or-`I₁` local support test. -/
theorem tamagawaProduct_eq_one_of_supported_primes (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (primes : List ℕ)
    (covers : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ e.Δ → p ∈ primes)
    (supported : primes.all (supportsTamagawaOne e) = true) :
    (e.baseChange ℚ).tamagawaProduct (R := ℤ) = 1 := by
  rw [WeierstrassCurve.tamagawaProduct_eq_prod _ ∅]
  · simp
  · intro v _
    let p := v.asIdeal.absNorm
    have hp : p.Prime := (Int.prime_absNorm v.asIdeal).mpr
      ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime)
    have hspan : v.asIdeal = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
    have localSupport : supportsTamagawaOne e p = true := by
      by_cases hd : (p : ℤ) ∣ e.Δ
      · exact List.all_eq_true.mp supported p (covers p hp hd)
      · simp [supportsTamagawaOne, hd]
    simp only [supportsTamagawaOne, Bool.or_eq_true, decide_eq_true_eq] at localSupport
    rcases localSupport with hd | ⟨hd, hd₂, hc⟩
    · apply tamagawaNumberAt_eq_one_of_unit_discriminant
      simpa using integerPlaceValuation_eq v p 0 e.Δ hspan (by simp) (by simpa using hd)
    · apply tamagawaNumberAt_eq_one_of_valuation_I_one
      · simpa using integerPlaceValuation_eq v p 1 e.Δ hspan (by simpa using hd) hd₂
      · simpa using integerPlaceValuation_eq v p 0 e.c₄ hspan (by simp) (by simpa using hc)

end VerifiedLcalc.EllipticCurve
