/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic
public import VerifiedLcalc.EllipticCurve.Tate.LocalReduction
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

private theorem completedIntegral (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    ((e.baseChange ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).IsIntegral
      ((rationalPlace p).adicCompletionIntegers ℚ) := by
  refine ⟨⟨e.baseChange _, ?_⟩⟩
  ext <;> simp [WeierstrassCurve.baseChange]

private theorem hasGoodReduction_completed (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] (hd : ¬ (p : ℤ) ∣ e.Δ) :
    ((e.baseChange ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).HasGoodReduction
      ((rationalPlace p).adicCompletionIntegers ℚ) := by
  let v := rationalPlace p
  let W := (e.baseChange ℚ).baseChange (v.adicCompletion ℚ)
  let R := v.adicCompletionIntegers ℚ
  let := completedIntegral e p
  have hΔ : W.Δ = (e.Δ : v.adicCompletion ℚ) := by
    simp only [W, WeierstrassCurve.baseChange, map_Δ, eq_intCast, map_intCast]
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation _ W.Δ = 1 := by
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ]
    exact completion_valuation_of_not_dvd p e.Δ hd
  let := isMinimal_of_valuation_Δ_eq_one R W hv
  exact ⟨hv⟩

private theorem tamagawaNumberAt_adicValued (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
      ((e.baseChange ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).tamagawaNumber
        (Valued.v : Valuation ((rationalPlace p).adicCompletion ℚ) (WithZero (Multiplicative ℤ))) := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let W := (e.baseChange ℚ).baseChange F
  rw [tamagawaNumberAt_def]
  convert W.tamagawaNumber_congr (ValuativeRel.valuation F)
    (ValuativeRel.isEquiv (ValuativeRel.valuation F) V) using 2
  dsimp only [W, WeierstrassCurve.baseChange]
  exact congrArg (fun f : ℚ →+* F => (e.baseChange ℚ).map f) (Subsingleton.elim _ _)

/-- The intrinsic local Tamagawa number is one at a good prime of the
checked model. The point-group index is taken over the completion. -/
theorem tamagawaNumberAt_eq_one_of_good_prime (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] (hd : ¬ (p : ℤ) ∣ e.Δ) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let W := (e.baseChange ℚ).baseChange F
  let : W.HasGoodReduction V.valuationSubring := hasGoodReduction_completed e p hd
  rw [tamagawaNumberAt_adicValued]
  exact W.tamagawaNumber_eq_one_of_hasGoodReduction V

private theorem completedSymbol_eq_I_one (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (hd : (p : ℤ) ∣ e.Δ)
    (hd₂ : ¬ (p : ℤ) ^ 2 ∣ e.Δ) (hc : ¬ (p : ℤ) ∣ e.c₄) :
    ((e.baseChange ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).reductionSymbol
      ((rationalPlace p).adicCompletionIntegers ℚ) = .I 1 := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := (e.baseChange ℚ).baseChange F
  let := completedIntegral e p
  have hΔ : W.Δ = (e.Δ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_Δ, eq_intCast, map_intCast]
  have hc₄ : W.c₄ = (e.c₄ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_c₄, eq_intCast, map_intCast]
  have hval := completion_intCast_valuation_eq p 1 e.Δ (by simpa using hd) hd₂
  have hcval : (IsDiscreteValuationRing.maximalIdeal R).valuation _ W.c₄ = 1 := by
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hc₄]
    exact completion_valuation_of_not_dvd p e.c₄ hc
  let := isMinimal_of_valuation_c₄_eq_one R W hcval
  have hmul : W.HasMultiplicativeReduction R := by
    refine ⟨?_, hcval⟩
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, hval]
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by decide)
  have hminval := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul R 1 (one_smul _ _)
  rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, hval] at hminval
  have hn : W.localMinimalDiscriminantValuation R = 1 := by
    exact_mod_cast neg_injective (WithZero.exp_injective hminval.symm)
  change W.reductionSymbol R = .I 1
  rw [W.reductionSymbol_eq_I_of_hasMultiplicativeReduction (R := R), hn]

/-- At multiplicative reduction with discriminant valuation one, the
intrinsic Tamagawa number is one in both splitting cases. -/
theorem tamagawaNumberAt_eq_one_of_multiplicative_index_one (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (hd : (p : ℤ) ∣ e.Δ)
    (hd₂ : ¬ (p : ℤ) ^ 2 ∣ e.Δ) (hc : ¬ (p : ℤ) ∣ e.c₄) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let R := V.valuationSubring
  let W := (e.baseChange ℚ).baseChange F
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := ℚ)).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  let : Finite (IsLocalRing.ResidueField R) := by
    change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
    infer_instance
  have hsymbol : W.reductionSymbol R = .I 1 := completedSymbol_eq_I_one e p hd hd₂ hc
  obtain ⟨C, D, ϖ, _, hD, hϖ, hterminal⟩ :=
    (W.reductionSymbol_eq_iff (R := R)).mp hsymbol
  have hspan : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  let : (C.baseChange F).IsElliptic := hD ▸ inferInstanceAs (D • W).IsElliptic
  have hlocal := (C.baseChange F).tamagawaNumber_eq_tateLocalIndex V hspan
    (by simpa only [integralModel_baseChange_self] using hterminal)
  rw [tamagawaNumberAt_adicValued]
  change W.tamagawaNumber V = 1
  rw [← W.tamagawaNumber_smul V D, hD, hlocal, integralModel_baseChange_self,
    tateLocalIndex_I_one]

/-- The exact Tamagawa factor is supported here at good reduction and at
multiplicative reduction of index one. -/
def supportsTamagawaOne (e : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  decide (¬ (p : ℤ) ∣ e.Δ) ||
    decide ((p : ℤ) ∣ e.Δ ∧ ¬ (p : ℤ) ^ 2 ∣ e.Δ ∧ ¬ (p : ℤ) ∣ e.c₄)

/-- The finite support test implies that the intrinsic Tamagawa factor is one. -/
theorem supportsTamagawaOne_correct (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (h : supportsTamagawaOne e p = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 := by
  simp only [supportsTamagawaOne, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hd | ⟨hd, hd₂, hc⟩
  · exact tamagawaNumberAt_eq_one_of_good_prime e p hd
  · exact tamagawaNumberAt_eq_one_of_multiplicative_index_one e p hd hd₂ hc

end VerifiedLcalc.EllipticCurve
