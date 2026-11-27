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
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Localization
import TauCeti.Data.Nat.Prime.IntCast
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.ZMod.Basic

/-! # Intrinsic Tamagawa numbers of rational curves

Good reduction and multiplicative reduction of index one both give the
intrinsic Tamagawa number one over the completed field. Multiplicative index
two and the checked terminal type III case both give factor two.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

open WeierstrassCurve NumberField IsDedekindDomain
open scoped WithZero

private theorem rationalPlace_asIdeal_span (p : ℕ) [Fact p.Prime] :
    (rationalPlace p).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  let v := rationalPlace p
  have hInt : (RationalPrimes.integerPlace v).asIdeal = Ideal.span {(p : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (RationalPrimes.integerPlace v).asIdeal,
      RationalPrimes.norm_integerPlace, rationalPlace_norm]
  have hMapped :
      Ideal.map Rat.ringOfIntegersEquiv.toRingHom v.asIdeal =
        Ideal.map Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(p : 𝓞 ℚ)}) := by
    calc
    v.asIdeal.map Rat.ringOfIntegersEquiv.toRingHom =
        (RationalPrimes.integerPlace v).asIdeal :=
      (RationalPrimes.integerPlace_asIdeal v).symm
    _ = Ideal.span {(p : ℤ)} := hInt
    _ = (Ideal.span {(p : 𝓞 ℚ)}).map Rat.ringOfIntegersEquiv.toRingHom := by
      rw [Ideal.map_span, Set.image_singleton]
      simp
  have hcomap := congrArg (Ideal.comap Rat.ringOfIntegersEquiv.toRingHom) hMapped
  simpa only [Ideal.comap_map_of_surjective Rat.ringOfIntegersEquiv.toRingHom
      Rat.ringOfIntegersEquiv.surjective,
    Ideal.comap_bot_of_injective Rat.ringOfIntegersEquiv.toRingHom
      Rat.ringOfIntegersEquiv.injective, sup_bot_eq] using hcomap

private theorem rationalLocalRing_maximalIdeal (p : ℕ) [Fact p.Prime] :
    IsLocalRing.maximalIdeal (RationalLocalRing p) =
      Ideal.span {(p : RationalLocalRing p)} := by
  let v := rationalPlace p
  let f := algebraMap (𝓞 ℚ) (RationalLocalRing p)
  calc
    _ = Ideal.map f v.asIdeal := (IsLocalization.AtPrime.map_eq_maximalIdeal
      v.asIdeal (RationalLocalRing p)).symm
    _ = Ideal.map f (Ideal.span {(p : 𝓞 ℚ)}) :=
      congrArg (Ideal.map f) (rationalPlace_asIdeal_span p)
    _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]

private theorem rationalCompletion_irreducible_natCast (p : ℕ) [Fact p.Prime] :
    Irreducible (p : (rationalPlace p).adicCompletionIntegers ℚ) := by
  let v := rationalPlace p
  have hloc : Irreducible (p : RationalLocalRing p) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      (rationalLocalRing_maximalIdeal p)
  simpa only [map_natCast] using
    (v.irreducible_localizationToCompletionIntegers_iff (K := ℚ)).mpr hloc

/-- At a rational prime, an integer prime to the residue characteristic
has normalized valuation one in the completion. -/
private theorem completion_valuation_of_not_dvd (p : ℕ) [Fact p.Prime] (n : ℤ)
    (h : ¬ (p : ℤ) ∣ n) :
    Valued.v (n : (rationalPlace p).adicCompletion ℚ) = 1 := by
  simpa using completion_intCast_valuation_eq p 0 n (by simp) (by simpa using h)

private theorem completion_valuation_lt_one_of_dvd (p : ℕ) [Fact p.Prime] (n : ℤ)
    (hn : n ≠ 0) (h : (p : ℤ) ∣ n) :
    Valued.v (n : (rationalPlace p).adicCompletion ℚ) < 1 := by
  let k := padicValNat p n.natAbs
  have hnabs : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hk : 0 < k := by
    have hk1 : 1 ≤ k := by
      simpa only [k, Nat.padicValNat_def] using
        (one_le_multiplicity_of_dvd hnabs (Int.natCast_dvd.mp h))
    omega
  have hdiv : (p : ℤ) ^ k ∣ n := by
    rw [← Nat.cast_pow, Int.natCast_dvd]
    exact (multiplicity_dvd_iff_le hnabs).mpr (by
      simp only [k, Nat.padicValNat_def, le_refl])
  have hnext : ¬ (p : ℤ) ^ (k + 1) ∣ n := by
    rw [← Nat.cast_pow, Int.natCast_dvd]
    simpa only [k, Nat.padicValNat_def] using
      (pow_succ_multiplicity_not_dvd (p := p) hnabs)
  rw [completion_intCast_valuation_eq p k n hdiv hnext]
  exact WithZero.exp_lt_exp.mpr (by omega)

private theorem finite_quotient_rationalPlace (p : ℕ) [Fact p.Prime] :
    Finite (𝓞 ℚ ⧸ (rationalPlace p).asIdeal) := by
  have hres : (𝓞 ℚ ⧸ (rationalPlace p).asIdeal) ≃+* ZMod p := by
    let h := idealQuotientEquivZMod (rationalPlace p)
    rw [rationalPlace_norm p] at h
    exact h
  exact Finite.of_equiv (ZMod p) hres.symm.toEquiv

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
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let S := v.adicCompletionIntegers ℚ
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

private theorem completedSymbol_eq_I (e : WeierstrassCurve ℤ) (v : HeightOneSpectrum R)
    [(e.baseChange ℚ).IsElliptic]
    (n : ℕ) (hn : 0 < n)
    (hd : Valued.v (e.Δ : v.adicCompletion ℚ) = WithZero.exp (-(n : ℤ)))
    (hc : Valued.v (e.c₄ : v.adicCompletion ℚ) = 1) :
    ((e.baseChange ℚ).baseChange (v.adicCompletion ℚ)).reductionSymbol
      (v.adicCompletionIntegers ℚ) = .I n := by
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
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hminval := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul S 1 (one_smul _ _)
  rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, hd] at hminval
  have hval : W.localMinimalDiscriminantValuation S = n := by
    exact_mod_cast neg_injective (WithZero.exp_injective hminval.symm)
  change W.reductionSymbol S = .I n
  rw [W.reductionSymbol_eq_I_of_hasMultiplicativeReduction (R := S), hval]

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
  have hsymbol : W.reductionSymbol S = .I 1 := completedSymbol_eq_I e v 1 (by decide) hd hc
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

/-- A supplied integral change whose image in the completed local integers is
a Tate terminal equation computes its local index on the original curve.
This is the shared model-to-completion transport used by the additive cases. -/
private theorem tamagawaNumberAt_eq_tateLocalIndex_of_terminal
    (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    [(e.baseChange ℚ).IsElliptic] (D : WeierstrassCurve.VariableChange ℤ)
    (symbol : TauCeti.ReductionSymbol)
    (hterminal : (D • e).IsTateTerminal (p : ℤ) symbol) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
      ((D • e).map
        (algebraMap ℤ ((rationalPlace p).adicCompletionIntegers ℚ))).tateLocalIndex
          (p : (rationalPlace p).adicCompletionIntegers ℚ) symbol := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let V : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let S := V.valuationSubring
  let C := (D • e).map (algebraMap ℤ S)
  let W := (e.baseChange ℚ).baseChange F
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S :=
    (v.isAdic_maximalIdeal_adicCompletionIntegers (K := ℚ)).isAdicComplete_iff.mpr
      ⟨inferInstance, inferInstance⟩
  let : Finite (IsLocalRing.ResidueField S) := by
    change Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
    infer_instance
  have hS : (ValuativeRel.valuation F).valuationSubring = S :=
    (Valuation.isEquiv_iff_valuationSubring (ValuativeRel.valuation F) V).mp
      (ValuativeRel.isEquiv (ValuativeRel.valuation F) V)
  let : HenselianLocalRing S := hS ▸ TauCeti.henselianLocalRing_valuationSubring F
  have hϖ : Irreducible (p : S) := rationalCompletion_irreducible_natCast p
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span {(p : S)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : S)).mp hϖ
  have hterminalC : C.IsTateTerminal (p : S) symbol := by
    let f := Int.castRingHom S
    have hdvd := (Fact.out : p.Prime).pow_dvd_intCast_iff
      (.of_ne_zero hϖ.ne_zero) hϖ.not_isUnit
    change ((D • e).map f).IsTateTerminal (p : S) symbol
    rw [← map_natCast f p,
      isTateTerminal_map_iff _ fun n x => by simpa [f] using hdvd n x]
    exact hterminal
  have hD : (D.baseChange F) • W = C.baseChange F := by
    have hw : W = e.baseChange F := by
      change e.map ((algebraMap ℚ F).comp (algebraMap ℤ ℚ)) = e.map (algebraMap ℤ F)
      exact congrArg e.map (IsScalarTower.algebraMap_eq ℤ ℚ F).symm
    calc
      (D.baseChange F) • W = (D.baseChange F) • e.baseChange F := by rw [hw]
      _ = (D • e).baseChange F := baseChange_smul_baseChange F D e
      _ = C.baseChange F := by
        change (D • e).map (algebraMap ℤ F) =
          ((D • e).map (algebraMap ℤ S)).map (algebraMap S F)
        rw [WeierstrassCurve.map_map]
        exact congrArg (D • e).map (IsScalarTower.algebraMap_eq ℤ S F)
  let : (C.baseChange F).IsElliptic := hD ▸ inferInstanceAs ((D.baseChange F) • W).IsElliptic
  have hlocal := (C.baseChange F).tamagawaNumber_eq_tateLocalIndex V hspan
    (by simpa only [integralModel_baseChange_self] using hterminalC)
  rw [tamagawaNumberAt_adicValued]
  change W.tamagawaNumber V = C.tateLocalIndex (p : S) symbol
  rw [← W.tamagawaNumber_smul V (D.baseChange F), hD, hlocal,
    integralModel_baseChange_self]

/-- A supplied tame type II terminal change gives the intrinsic factor one.
The displayed scale-one change is checked exactly; this theorem discovers no
normalization. -/
theorem tamagawaNumberAt_eq_one_of_typeII_shift (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (shift : TamagawaTypeIIShift) (hcheck : checkTameTypeII e p shift = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 := by
  have h' : 3 < p ∧ (p : ℤ) ∣ (typeIIChange shift • e).b₂ ∧
      (p : ℤ) ∣ (typeIIChange shift • e).a₃ ∧
      (p : ℤ) ∣ (typeIIChange shift • e).a₄ ∧
      (p : ℤ) ∣ (typeIIChange shift • e).a₆ ∧
      ¬ (p : ℤ) ^ 2 ∣ (typeIIChange shift • e).a₆ := by
    simpa [checkTameTypeII] using hcheck
  have hterminal : (typeIIChange shift • e).IsTateTerminal (p : ℤ) .II := by
    rw [isTateTerminal_II]
    exact ⟨h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2⟩
  calc
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
        ((typeIIChange shift • e).map
          (algebraMap ℤ ((rationalPlace p).adicCompletionIntegers ℚ))).tateLocalIndex
            (p : (rationalPlace p).adicCompletionIntegers ℚ) .II :=
      tamagawaNumberAt_eq_tateLocalIndex_of_terminal e p (typeIIChange shift) .II hterminal
    _ = 1 := tateLocalIndex_II

/-- A terminal predicate on an integer equation transfers to the completed
integer ring when the rational prime remains its uniformizer. -/
private theorem isTateTerminal_baseChange_int {R : Type*} [CommRing R] [IsDomain R]
    (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hϖ : Irreducible (p : R)) {symbol : TauCeti.ReductionSymbol}
    (h : e.IsTateTerminal (p : ℤ) symbol) :
    (e.baseChange R).IsTateTerminal (p : R) symbol := by
  let f := Int.castRingHom R
  have hdvd := (Fact.out : p.Prime).pow_dvd_intCast_iff
    (.of_ne_zero hϖ.ne_zero) hϖ.not_isUnit
  change (e.map f).IsTateTerminal (p : R) symbol
  rw [← map_natCast f p, isTateTerminal_map_iff _ fun n x => by simpa [f] using hdvd n x]
  exact h

private theorem cast_divisor_mul_quotient {R : Type*} [CommRing R] {p k : ℕ} {x : ℤ}
    (h : (p : ℤ) ^ k ∣ x) :
    (x : R) = (p : R) ^ k * ((x / (p : ℤ) ^ k : ℤ) : R) := by
  rw [← Int.cast_natCast p, ← Int.cast_pow, ← Int.cast_mul, mul_comm,
    Int.ediv_mul_cancel_of_dvd h]

private theorem map_residue_intCast {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ}
    (f : IsLocalRing.ResidueField R ≃+* ZMod p) (x : ℤ) :
    f (IsLocalRing.residue R (x : R)) = (x : ZMod p) :=
  map_intCast (f.toRingHom.comp (IsLocalRing.residue R)) x

/-- The completed type IV Tate root condition is equivalent to a root of the
derived finite quadratic. Its coefficients are the quotients of the submitted
terminal model, not separately trusted payload values. -/
private theorem hasTateYRoot_iff_typeIVResiduePolynomial
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (p : ℕ)
    (f : IsLocalRing.ResidueField R ≃+* ZMod p) (e : WeierstrassCurve ℤ)
    (hspan : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)})
    (hp : (p : R) ≠ 0) (h₃ : (p : ℤ) ∣ e.a₃) (h₆ : (p : ℤ) ^ 2 ∣ e.a₆) :
    (e.baseChange R).HasTateYRoot (p : R) 1 ↔
      ∃ y : ZMod p, typeIVResiduePolynomial e p y = 0 := by
  have ha₃ : (e.baseChange R).a₃ = (p : R) ^ 1 * ((e.a₃ / (p : ℤ) : ℤ) : R) := by
    change (e.a₃ : R) = _
    simpa only [pow_one] using
      cast_divisor_mul_quotient (R := R) (k := 1) (by simpa using h₃)
  have ha₆ : (e.baseChange R).a₆ = (p : R) ^ 2 * ((e.a₆ / (p : ℤ) ^ 2 : ℤ) : R) := by
    change (e.a₆ : R) = _
    exact cast_divisor_mul_quotient h₆
  rw [hasTateYRoot_iff_exists_residue_root hspan hp ha₃ ha₆]
  refine f.toEquiv.exists_congr fun y => ?_
  rw [← f.map_eq_zero_iff]
  simp only [map_sub, map_add, map_mul, map_pow, map_residue_intCast,
    typeIVResiduePolynomial]
  rfl

/-- Euler's nonsquare certificate excludes roots of the type IV quadratic over
an odd prime field. -/
private theorem no_typeIV_residue_root_of_euler_power (p : ℕ) [Fact p.Prime]
    (hp : 3 < p) (b₃ b₆ : ℤ)
    (hpow : ((b₃ ^ 2 + 4 * b₆ : ℤ) : ZMod p) ^ ((p - 1) / 2) = -1) :
    ¬ ∃ y : ZMod p, y ^ 2 + (b₃ : ZMod p) * y - (b₆ : ZMod p) = 0 := by
  rintro ⟨y, hy⟩
  let d : ZMod p := ((b₃ ^ 2 + 4 * b₆ : ℤ) : ZMod p)
  let z : ZMod p := 2 * y + (b₃ : ZMod p)
  have hdisc : ((b₃ ^ 2 + 4 * b₆ : ℤ) : ZMod p) =
      (b₃ : ZMod p) ^ 2 + 4 * (b₆ : ZMod p) := by push_cast; ring
  have hsq : z ^ 2 = d := by
    dsimp [z, d]
    calc
      (2 * y + (b₃ : ZMod p)) ^ 2 =
          4 * (y ^ 2 + (b₃ : ZMod p) * y - (b₆ : ZMod p)) +
            ((b₃ ^ 2 + 4 * b₆ : ℤ) : ZMod p) := by rw [hdisc]; ring
      _ = ((b₃ ^ 2 + 4 * b₆ : ℤ) : ZMod p) := by rw [hy]; ring
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  have hodd : p / 2 = (p - 1) / 2 := by obtain ⟨k, hk⟩ := hpodd; omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have hcharValue : quadraticChar (ZMod p) d = -1 := by
    have hpowD : d ^ ((p - 1) / 2) = -1 := by simpa [d] using hpow
    have hd : d ≠ 0 := by
      intro hz
      rw [hz] at hpowD
      have hexp : 0 < (p - 1) / 2 := by omega
      rw [zero_pow hexp.ne'] at hpowD
      norm_num at hpowD
    have hpowNe : d ^ (Fintype.card (ZMod p) / 2) ≠ 1 := by
      rw [ZMod.card, hodd, hpowD]
      have hne : (-1 : ZMod p) ≠ 1 := by
        have : Fact (2 < p) := ⟨by omega⟩
        exact ZMod.neg_one_ne_one
      exact hne
    rw [quadraticChar_eq_pow_of_char_ne_two hchar hd, ite_eq_right hpowNe]
  have hnotSquare : ¬ IsSquare d :=
    (quadraticChar_neg_one_iff_not_isSquare).mp hcharValue
  exact hnotSquare ⟨z, by simpa [pow_two] using hsq.symm⟩

/-- At multiplicative reduction with discriminant valuation two, the intrinsic
Tamagawa number is two in both splitting cases. -/
theorem tamagawaNumberAt_eq_two_of_valuation_I_two (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (hd : Valued.v (e.Δ : (rationalPlace p).adicCompletion ℚ) = WithZero.exp (-2 : ℤ))
    (hc : Valued.v (e.c₄ : (rationalPlace p).adicCompletion ℚ) = 1) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 2 := by
  let v := rationalPlace p
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
  have hsymbol : W.reductionSymbol S = .I 2 := completedSymbol_eq_I e v 2 (by decide) hd hc
  obtain ⟨C, D, ϖ, _, hD, hϖ, hterminal⟩ := (W.reductionSymbol_eq_iff (R := S)).mp hsymbol
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  let : (C.baseChange F).IsElliptic := hD ▸ inferInstanceAs (D • W).IsElliptic
  have hlocal := (C.baseChange F).tamagawaNumber_eq_tateLocalIndex V hspan
    (by simpa only [integralModel_baseChange_self] using hterminal)
  have hindex : C.tateLocalIndex ϖ (.I 2) = 2 := by
    by_cases hroot : C.HasTateTangentRoot ϖ
    · simpa using (tateLocalIndex_I_add_one_of_hasTateTangentRoot hroot 1)
    · simpa using (tateLocalIndex_I_add_one_of_not_hasTateTangentRoot hroot 1)
  rw [tamagawaNumberAt_adicValued]
  change W.tamagawaNumber V = 2
  rw [← W.tamagawaNumber_smul V D, hD, hlocal, integralModel_baseChange_self,
    hindex]

/-- A supplied integral variable change whose model satisfies Tate's terminal
type III divisibilities gives intrinsic Tamagawa factor two. The only input is
the exact checked terminal model; no classification from invariant valuations
is asserted. -/
theorem tamagawaNumberAt_eq_two_of_typeIII_shift (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (D : WeierstrassCurve.VariableChange ℤ)
    (hb₂ : (p : ℤ) ∣ (D • e).b₂)
    (ha₃ : (p : ℤ) ∣ (D • e).a₃)
    (ha₄ : (p : ℤ) ∣ (D • e).a₄)
    (ha₆ : (p : ℤ) ^ 2 ∣ (D • e).a₆)
    (hb₈ : ¬ (p : ℤ) ^ 3 ∣ (D • e).b₈) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 2 := by
  have hterminal : (D • e).IsTateTerminal (p : ℤ) .III := by
    rw [isTateTerminal_III]
    exact ⟨hb₂, ha₃, ha₄, ha₆, hb₈⟩
  calc
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
        ((D • e).map
          (algebraMap ℤ ((rationalPlace p).adicCompletionIntegers ℚ))).tateLocalIndex
            (p : (rationalPlace p).adicCompletionIntegers ℚ) .III :=
      tamagawaNumberAt_eq_tateLocalIndex_of_terminal e p D .III hterminal
    _ = 2 := tateLocalIndex_III

/-- The supplied type IV translation and residue certificate determine the
intrinsic local factor: three for a checked root, one for a checked nonsplit
Euler value. No root or normalization is discovered by this theorem. -/
theorem tamagawaNumberAt_eq_typeIV_of_evidence (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (evidence : TamagawaTypeIVEvidence) (hcheck : checkTameTypeIV e p evidence = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
      match evidence.residue with
      | .root _ => 3
      | .nonsplitEulerPower _ => 1 := by
  let D := typeIVChange evidence
  let A := D • e
  let v := rationalPlace p
  let S := v.adicCompletionIntegers ℚ
  let hϖ : Irreducible (p : S) := rationalCompletion_irreducible_natCast p
  let f := completionResidueEquiv p
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span {(p : S)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : S)).mp hϖ
  cases he : evidence.residue with
  | root y =>
    have hcheck' :
        (decide (3 < p ∧ (p : ℤ) ∣ A.b₂ ∧ (p : ℤ) ∣ A.a₃ ∧
          (p : ℤ) ∣ A.a₄ ∧ (p : ℤ) ^ 2 ∣ A.a₆ ∧
          (p : ℤ) ^ 3 ∣ A.b₈ ∧ ¬ (p : ℤ) ^ 3 ∣ A.b₆) &&
        decide (y < p ∧ typeIVResiduePolynomial A p (y : ZMod p) = 0)) = true := by
      simp only [checkTameTypeIV, typeIVChange, he] at hcheck
      exact hcheck
    rcases Bool.and_eq_true_iff.mp hcheck' with ⟨ht, hroot⟩
    have ht' : 3 < p ∧ (p : ℤ) ∣ A.b₂ ∧ (p : ℤ) ∣ A.a₃ ∧
        (p : ℤ) ∣ A.a₄ ∧ (p : ℤ) ^ 2 ∣ A.a₆ ∧
        (p : ℤ) ^ 3 ∣ A.b₈ ∧ ¬ (p : ℤ) ^ 3 ∣ A.b₆ := of_decide_eq_true ht
    have hroot' : y < p ∧ typeIVResiduePolynomial A p (y : ZMod p) = 0 :=
      of_decide_eq_true hroot
    have hterminalInt : A.IsTateTerminal (p : ℤ) .IV := by
      rw [isTateTerminal_IV]
      exact ⟨ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2.1,
        ht'.2.2.2.2.2.1, ht'.2.2.2.2.2.2⟩
    have hrootIff := hasTateYRoot_iff_typeIVResiduePolynomial p f A hspan hϖ.ne_zero
      ht'.2.2.1 ht'.2.2.2.2.1
    have hrootTate : (A.baseChange S).HasTateYRoot (p : S) 1 :=
      hrootIff.mpr ⟨(y : ZMod p), hroot'.2⟩
    calc
      (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
          (A.baseChange S).tateLocalIndex (p : S) .IV :=
        tamagawaNumberAt_eq_tateLocalIndex_of_terminal e p D .IV hterminalInt
      _ = 3 := tateLocalIndex_IV_of_hasTateYRoot hrootTate
  | nonsplitEulerPower value =>
    have hcheck' :
        (decide (3 < p ∧ (p : ℤ) ∣ A.b₂ ∧ (p : ℤ) ∣ A.a₃ ∧
          (p : ℤ) ∣ A.a₄ ∧ (p : ℤ) ^ 2 ∣ A.a₆ ∧
          (p : ℤ) ^ 3 ∣ A.b₈ ∧ ¬ (p : ℤ) ^ 3 ∣ A.b₆) &&
        decide (value + 1 = p ∧
          (((A.a₃ / (p : ℤ)) ^ 2 + 4 * (A.a₆ / (p : ℤ) ^ 2) : ℤ) : ZMod p) ^
            ((p - 1) / 2) = -1)) = true := by
      simp only [checkTameTypeIV, typeIVChange, he] at hcheck
      exact hcheck
    rcases Bool.and_eq_true_iff.mp hcheck' with ⟨ht, heuler⟩
    have ht' : 3 < p ∧ (p : ℤ) ∣ A.b₂ ∧ (p : ℤ) ∣ A.a₃ ∧
        (p : ℤ) ∣ A.a₄ ∧ (p : ℤ) ^ 2 ∣ A.a₆ ∧
        (p : ℤ) ^ 3 ∣ A.b₈ ∧ ¬ (p : ℤ) ^ 3 ∣ A.b₆ := of_decide_eq_true ht
    have heuler' : value + 1 = p ∧
        (((A.a₃ / (p : ℤ)) ^ 2 + 4 * (A.a₆ / (p : ℤ) ^ 2) : ℤ) : ZMod p) ^
          ((p - 1) / 2) = -1 := of_decide_eq_true heuler
    have hterminalInt : A.IsTateTerminal (p : ℤ) .IV := by
      rw [isTateTerminal_IV]
      exact ⟨ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2.1,
        ht'.2.2.2.2.2.1, ht'.2.2.2.2.2.2⟩
    have hrootIff := hasTateYRoot_iff_typeIVResiduePolynomial p f A hspan hϖ.ne_zero
      ht'.2.2.1 ht'.2.2.2.2.1
    have hnotRootFinite : ¬ ∃ y : ZMod p, typeIVResiduePolynomial A p y = 0 :=
      no_typeIV_residue_root_of_euler_power p ht'.1 (A.a₃ / (p : ℤ))
        (A.a₆ / (p : ℤ) ^ 2) heuler'.2
    have hnotRootTate : ¬ (A.baseChange S).HasTateYRoot (p : S) 1 :=
      fun hroot => hnotRootFinite (hrootIff.mp hroot)
    calc
      (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
          (A.baseChange S).tateLocalIndex (p : S) .IV :=
        tamagawaNumberAt_eq_tateLocalIndex_of_terminal e p D .IV hterminalInt
      _ = 1 := tateLocalIndex_IV_of_not_hasTateYRoot hnotRootTate

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

/-- Discriminant valuation two and unit c₄ give multiplicative reduction of
type `I₂`, whose local index is two in either splitting case. -/
theorem tamagawaNumberAt_eq_two_of_multiplicative_index_two (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (hd₂ : (p : ℤ) ^ 2 ∣ e.Δ) (hd₃ : ¬ (p : ℤ) ^ 3 ∣ e.Δ)
    (hc : ¬ (p : ℤ) ∣ e.c₄) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 2 :=
  tamagawaNumberAt_eq_two_of_valuation_I_two e p
    (by simpa using completion_intCast_valuation_eq p 2 e.Δ (by simpa using hd₂) hd₃)
    (completion_valuation_of_not_dvd p e.c₄ hc)

private theorem hasSplitMultiplicativeReduction_completion_iff_nodePolynomial
    (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hm : ((e.baseChange ℚ).baseChange
      ((rationalPlace p).adicCompletion ℚ)).HasMultiplicativeReduction
        ((rationalPlace p).adicCompletionIntegers ℚ)) :
    ((e.baseChange ℚ).baseChange
      ((rationalPlace p).adicCompletion ℚ)).HasSplitMultiplicativeReduction
        ((rationalPlace p).adicCompletionIntegers ℚ) ↔
      (e.baseChange (ZMod p)).nodePolynomial.Splits := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  let W := e.baseChange S
  let U := W.baseChange F
  let k := completionResidueEquiv p
  have hU : U = (e.baseChange ℚ).baseChange F := by
    ext <;> simp [U, W, WeierstrassCurve.baseChange]
  have hmU : U.HasMultiplicativeReduction S := by
    simpa only [hU] using hm
  let : IsMinimal S U := hmU.toIsMinimal
  have hreduce : (U.reduction S).map k.toRingHom = e.baseChange (ZMod p) := by
    rw [WeierstrassCurve.reduction, WeierstrassCurve.integralModel_baseChange_self]
    ext <;> simp [W, WeierstrassCurve.baseChange]
  have hsplitU : U.HasSplitMultiplicativeReduction S ↔
      (e.baseChange (ZMod p)).nodePolynomial.Splits := by
    rw [← hmU.splits_nodePolynomial_reduction_iff S, ← hreduce,
      WeierstrassCurve.map_nodePolynomial]
    exact ⟨fun hs => hs.map k.toRingHom,
      fun hs => hs.of_splits_map k.toRingHom (fun x _ => k.surjective x)⟩
  constructor
  · intro hs
    exact hsplitU.mp (by simpa only [hU] using hs)
  · intro hs
    simpa only [hU] using hsplitU.mpr hs

private theorem completedHasMultiplicativeReduction_of_valuation
    (e : WeierstrassCurve ℤ) (p n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (hd : Valued.v (e.Δ : (rationalPlace p).adicCompletion ℚ) =
      WithZero.exp (-(n : ℤ)))
    (hc : Valued.v (e.c₄ : (rationalPlace p).adicCompletion ℚ) = 1) :
    ((e.baseChange ℚ).baseChange
      ((rationalPlace p).adicCompletion ℚ)).HasMultiplicativeReduction
        ((rationalPlace p).adicCompletionIntegers ℚ) := by
  let v := rationalPlace p
  let F := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  let W := (e.baseChange ℚ).baseChange F
  have hΔ : W.Δ = (e.Δ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_Δ, eq_intCast, map_intCast]
  have hc₄ : W.c₄ = (e.c₄ : F) := by
    simp only [W, WeierstrassCurve.baseChange, map_c₄, eq_intCast, map_intCast]
  have hcval : (IsDiscreteValuationRing.maximalIdeal S).valuation _ W.c₄ = 1 := by
    rw [v.valuation_maximalIdeal_adicCompletionIntegers, hc₄, hc]
  let : IsIntegral S W := completedIntegral e v
  let : IsMinimal S W := isMinimal_of_valuation_c₄_eq_one S W hcval
  refine ⟨?_, hcval⟩
  rw [v.valuation_maximalIdeal_adicCompletionIntegers, hΔ, hd, ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.mpr (by omega)

private theorem tamagawaNumberAt_eq_of_multiplicative_valuation
    (e : WeierstrassCurve ℤ) (p n : ℕ) [Fact p.Prime]
    [(e.baseChange ℚ).IsElliptic] (hn : 0 < n)
    (hd : Valued.v (e.Δ : (rationalPlace p).adicCompletion ℚ) =
      WithZero.exp (-(n : ℤ)))
    (hc : Valued.v (e.c₄ : (rationalPlace p).adicCompletion ℚ) = 1)
    (split : Bool)
    (hs : (e.baseChange (ZMod p)).nodePolynomial.Splits ↔ split = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
      if split then n else Nat.gcd 2 n := by
  let v := rationalPlace p
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
  have hsymbol : W.reductionSymbol S = .I n := completedSymbol_eq_I e v n hn hd hc
  obtain ⟨C, D, ϖ, hmin, hD, hϖ, hterminal⟩ := (W.reductionSymbol_eq_iff (R := S)).mp hsymbol
  have hspan : IsLocalRing.maximalIdeal S = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  let : (C.baseChange F).IsElliptic := hD ▸ inferInstanceAs (D • W).IsElliptic
  let : IsMinimal S (C.baseChange F) := hmin
  have hmulW := completedHasMultiplicativeReduction_of_valuation e p n hn hd hc
  let : IsMinimal S W := hmulW.toIsMinimal
  have hsplitW : W.HasSplitMultiplicativeReduction S ↔ split = true :=
    (hasSplitMultiplicativeReduction_completion_iff_nodePolynomial e p hmulW).trans hs
  have hsplitC : (C.baseChange F).HasSplitMultiplicativeReduction S ↔ split = true := by
    constructor
    · intro hcSplit
      have hDinv : D⁻¹ • C.baseChange F = W := by
        rw [← hD, inv_smul_smul]
      exact hsplitW.mp (HasSplitMultiplicativeReduction.of_isMinimal_smul S D⁻¹ hDinv hcSplit)
    · intro hsplit
      exact HasSplitMultiplicativeReduction.of_isMinimal_smul S D hD (hsplitW.mpr hsplit)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hlocal := (C.baseChange F).tamagawaNumber_eq_tateLocalIndex V hspan
    (by simpa only [integralModel_baseChange_self] using hterminal)
  have hindex : C.tateLocalIndex ϖ (.I (m + 1)) =
      if split then m + 1 else Nat.gcd 2 (m + 1) := by
    by_cases hsplit : split = true
    · rw [ite_eq_left hsplit]
      exact hterminal.tateLocalIndex_of_hasSplitMultiplicativeReduction hϖ (hsplitC.mpr hsplit)
    · rw [ite_eq_right hsplit]
      exact hterminal.tateLocalIndex_of_not_hasSplitMultiplicativeReduction hϖ
        (fun hsplitC' => hsplit ((hsplitC.mp hsplitC')))
  rw [tamagawaNumberAt_adicValued]
  change W.tamagawaNumber V = if split then m + 1 else Nat.gcd 2 (m + 1)
  rw [← W.tamagawaNumber_smul V D, hD, hlocal, integralModel_baseChange_self, hindex]

private theorem nodePolynomial_not_splits_of_euler_power (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hpow : (((-(e.c₄ * e.c₆) : ℤ) : ZMod p) ^ ((p - 1) / 2)) = -1) :
    ¬ (e.baseChange (ZMod p)).nodePolynomial.Splits := by
  let R := ZMod p
  let disc : R := (-(e.c₄ * e.c₆) : ℤ)
  have hchar : ringChar R ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  let : Fact (2 < p) := ⟨hp⟩
  have hpowDisc : disc ^ ((p - 1) / 2) = -1 := by
    simpa [disc] using hpow
  have hdisc : disc ≠ 0 := by
    intro hz
    have hexp : 0 < (p - 1) / 2 := by omega
    rw [hz, zero_pow hexp.ne'] at hpowDisc
    norm_num at hpowDisc
  have hpow' : disc ^ (Fintype.card R / 2) = -1 := by
    have hcard : Fintype.card R = p := by simp [R]
    have hpNeTwo : p ≠ 2 := by omega
    have hpOddMod : p % 2 = 1 :=
      (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hpNeTwo
    have hexp : (p - 1) / 2 = p / 2 := by omega
    rw [hcard, ← hexp]
    exact hpowDisc
  have hpowNeOne : disc ^ (Fintype.card R / 2) ≠ 1 := by
    rw [hpow']
    exact ZMod.neg_one_ne_one
  have hcharValue : quadraticChar R disc = -1 := by
    rw [quadraticChar_eq_pow_of_char_ne_two hchar hdisc, ite_eq_right hpowNeOne]
  have hnotSquare : ¬ IsSquare disc :=
    (quadraticChar_neg_one_iff_not_isSquare).mp hcharValue
  have : NeZero (2 : R) := ⟨by
    intro hzero
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hpNat : p ∣ 2 := by exact_mod_cast hdiv
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by decide) hpNat
    omega⟩
  have hsplitSquare :=
    (e.baseChange R).splits_nodePolynomial_map_iff_isSquare (RingHom.id R)
  intro hsplit
  apply hnotSquare
  have hsplit' : (Polynomial.map (RingHom.id R)
      (e.baseChange R).nodePolynomial).Splits := by
    simpa [R, WeierstrassCurve.baseChange, map_nodePolynomial] using hsplit
  simpa [disc, R, WeierstrassCurve.baseChange, map_c₄, map_c₆] using
    hsplitSquare.mp hsplit'

private theorem tamagawaNumberAt_eq_of_multiplicative_evidence
    (e : WeierstrassCurve ℤ) (p n : ℕ) [Fact p.Prime]
    [(e.baseChange ℚ).IsElliptic] (hn : 0 < n)
    (hpadic : n = padicValNat p e.Δ.natAbs)
    (hd : Valued.v (e.Δ : (rationalPlace p).adicCompletion ℚ) =
      WithZero.exp (-(n : ℤ)))
    (hc : Valued.v (e.c₄ : (rationalPlace p).adicCompletion ℚ) = 1)
    (evidence : TamagawaSplittingEvidence)
    (hevidence : checkTamagawaSplitting e p evidence = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) =
      multiplicativeTamagawaFactor e p evidence := by
  cases evidence with
  | root value =>
    have hrootData : 2 < p ∧ value < p ∧
        nodeValue e value % (p : ℤ) = 0 := by
      simpa [checkTamagawaSplitting] using hevidence
    have hrootEval : (e.baseChange (ZMod p)).nodePolynomial.eval
        (value : ZMod p) = 0 := by
      rw [nodeValue_correct]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
        (Int.dvd_iff_emod_eq_zero.mpr hrootData.2.2)
    have hroot : hasNodeRoot e p = true := by
      apply (hasNodeRoot_correct e p).2
      exact ⟨(value : ZMod p), hrootEval⟩
    have hc' : (e.baseChange (ZMod p)).c₄ ≠ 0 := by
      have hcne : e.c₄ ≠ 0 := by
        intro hz
        rw [hz] at hc
        norm_num at hc
      have h : ¬ (p : ℤ) ∣ e.c₄ := by
        intro hdiv
        have hval := completion_valuation_lt_one_of_dvd p e.c₄ hcne hdiv
        rw [hc] at hval
        norm_num at hval
      simpa only [WeierstrassCurve.baseChange, map_c₄, eq_intCast,
        ZMod.intCast_zmod_eq_zero_iff_dvd, ne_eq] using h
    have hsplit := (hasNodeRoot_iff_splits e p hc').mp hroot
    simpa [multiplicativeTamagawaFactor, hpadic] using
      tamagawaNumberAt_eq_of_multiplicative_valuation e p n hn hd hc true
        ⟨fun _ => rfl, fun _ => hsplit⟩
  | nonsplitEulerPower value =>
    have hdata : 2 < p ∧ value + 1 = p ∧
        (((-(e.c₄ * e.c₆) : ℤ) : ZMod p) ^ ((p - 1) / 2)) = -1 := by
      simpa [checkTamagawaSplitting] using hevidence
    have hnotsplit := nodePolynomial_not_splits_of_euler_power e p hdata.1 hdata.2.2
    simpa [multiplicativeTamagawaFactor, hpadic] using
      tamagawaNumberAt_eq_of_multiplicative_valuation e p n hn hd hc false
        ⟨fun hs => False.elim (hnotsplit hs), fun hfalse => by cases hfalse⟩

/-- The finite support test implies that the intrinsic Tamagawa factor is one. -/
theorem supportsTamagawaOne_correct (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] [(e.baseChange ℚ).IsElliptic]
    (h : supportsTamagawaOne e p = true) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = 1 := by
  simp only [supportsTamagawaOne, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hd | ⟨hd, hd₂, hc⟩
  · exact tamagawaNumberAt_eq_one_of_good_prime e p hd
  · exact tamagawaNumberAt_eq_one_of_multiplicative_index_one e p hd hd₂ hc

/-- Every non-`none` result of the supported Tamagawa computation is the
intrinsic local Tamagawa number at the completed place. -/
private theorem tamagawaExpected_base_correct (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    [(e.baseChange ℚ).IsElliptic] {shift : Option TamagawaTypeIIIShift}
    {typeIV : Option TamagawaTypeIVEvidence}
    {splitting : Option TamagawaSplittingEvidence} {value : ℕ}
    (h : tamagawaExpected? e p shift typeIV none splitting = some value) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = value := by
  cases splitting with
  | none =>
    cases shift with
    | some shift =>
      cases typeIV with
      | some evidence => simp [tamagawaExpected?] at h
      | none =>
        by_cases ht : checkTameTypeIII e p shift = true
        · rw [tamagawaExpected?, ht] at h
          cases h
          have ht' : 3 < p ∧ (p : ℤ) ∣ (typeIIIChange shift • e).b₂ ∧
              (p : ℤ) ∣ (typeIIIChange shift • e).a₃ ∧
              (p : ℤ) ∣ (typeIIIChange shift • e).a₄ ∧
              (p : ℤ) ^ 2 ∣ (typeIIIChange shift • e).a₆ ∧
              ¬ (p : ℤ) ^ 3 ∣ (typeIIIChange shift • e).b₈ := by
            simpa [checkTameTypeIII] using ht
          exact tamagawaNumberAt_eq_two_of_typeIII_shift e p (typeIIIChange shift)
            ht'.2.1 ht'.2.2.1 ht'.2.2.2.1 ht'.2.2.2.2.1 ht'.2.2.2.2.2
        · simp [tamagawaExpected?, ht] at h
    | none =>
      cases typeIV with
      | some evidence =>
        by_cases ht : checkTameTypeIV e p evidence = true
        · rw [tamagawaExpected?, ht] at h
          cases h
          exact tamagawaNumberAt_eq_typeIV_of_evidence e p evidence ht
        · simp [tamagawaExpected?, ht] at h
      | none =>
        by_cases hs : supportsTamagawaOne e p = true
        · rw [tamagawaExpected?, hs] at h
          cases h
          exact supportsTamagawaOne_correct e p hs
        · by_cases hm : multiplicativeIndexTwo e p = true
          · have hsf : supportsTamagawaOne e p = false := Bool.eq_false_of_not_eq_true hs
            rw [tamagawaExpected?, hsf, hm] at h
            cases h
            have hm' : (p : ℤ) ^ 2 ∣ e.Δ ∧ ¬ (p : ℤ) ^ 3 ∣ e.Δ ∧
                ¬ (p : ℤ) ∣ e.c₄ := by
              simpa [multiplicativeIndexTwo] using hm
            exact tamagawaNumberAt_eq_two_of_multiplicative_index_two e p
              hm'.1 hm'.2.1 hm'.2.2
          · have hsf : supportsTamagawaOne e p = false := Bool.eq_false_of_not_eq_true hs
            have hmf : multiplicativeIndexTwo e p = false := Bool.eq_false_of_not_eq_true hm
            simp [tamagawaExpected?, hsf, hmf] at h
  | some splitEvidence =>
    cases shift with
    | some _ =>
      cases typeIV with
      | some _ => simp [tamagawaExpected?] at h
      | none =>
        change (none : Option ℕ) = some value at h
        cases h
    | none =>
      cases typeIV with
      | some _ => simp [tamagawaExpected?] at h
      | none =>
        by_cases hs : supportsTamagawaOne e p = true
        · simp [tamagawaExpected?, hs] at h
        · by_cases hm : multiplicativeIndexTwo e p = true
          · simp [tamagawaExpected?, hs, hm] at h
          · by_cases hc : (p : ℤ) ∣ e.c₄
            · simp [tamagawaExpected?, hs, hm, hc] at h
            · by_cases hcheck : checkTamagawaSplitting e p splitEvidence = true
              · have hval : value = multiplicativeTamagawaFactor e p splitEvidence := by
                  simpa [tamagawaExpected?, hs, hm, hc, hcheck] using h.symm
                have hbad : (p : ℤ) ∣ e.Δ := by
                  by_contra hnot
                  apply hs
                  simp [supportsTamagawaOne, hnot]
                let n := padicValNat p e.Δ.natAbs
                have hΔne : e.Δ ≠ 0 := by
                  have hunit : IsUnit ((e.baseChange ℚ).Δ) := by
                    rcases ‹(e.baseChange ℚ).IsElliptic› with ⟨hunit⟩
                    exact hunit
                  have hQ : (e.Δ : ℚ) ≠ 0 := by
                    simpa only [WeierstrassCurve.baseChange, map_Δ, eq_intCast] using
                      hunit.ne_zero
                  exact_mod_cast hQ
                have hnabs : e.Δ.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hΔne
                have hn : 0 < n := by
                  have hn1 : 1 ≤ n := by
                    simpa only [n, Nat.padicValNat_def] using
                      (one_le_multiplicity_of_dvd hnabs (Int.natCast_dvd.mp hbad))
                  omega
                have hdiv : (p : ℤ) ^ n ∣ e.Δ := by
                  rw [← Nat.cast_pow, Int.natCast_dvd]
                  exact (multiplicity_dvd_iff_le hnabs).mpr
                    (by simp only [n, Nat.padicValNat_def, le_refl])
                have hnext : ¬ (p : ℤ) ^ (n + 1) ∣ e.Δ := by
                  rw [← Nat.cast_pow, Int.natCast_dvd]
                  simpa only [n, Nat.padicValNat_def] using
                    (pow_succ_multiplicity_not_dvd (p := p) hnabs)
                have hdivNat : p ^ n ∣ e.Δ.natAbs := by
                  rw [← Nat.cast_pow, Int.natCast_dvd] at hdiv
                  exact hdiv
                have hnotNat : ¬ p ^ (n + 1) ∣ e.Δ.natAbs := by
                  intro hpow
                  apply hnext
                  rw [← Nat.cast_pow, Int.natCast_dvd]
                  exact hpow
                have hpadic : n = padicValNat p e.Δ.natAbs := by
                  have hlo : n ≤ padicValNat p e.Δ.natAbs := by
                    simpa only [Nat.padicValNat_def] using
                      (multiplicity_dvd_iff_le hnabs).mp hdivNat
                  have hhi : ¬ n + 1 ≤ padicValNat p e.Δ.natAbs := by
                    intro hle
                    apply hnotNat
                    exact (multiplicity_dvd_iff_le hnabs).mpr (by
                      simpa only [Nat.padicValNat_def] using hle)
                  omega
                have hdval := completion_intCast_valuation_eq p n e.Δ hdiv hnext
                have hcval := completion_valuation_of_not_dvd p e.c₄ hc
                have hfactor := tamagawaNumberAt_eq_of_multiplicative_evidence
                  e p n hn hpadic hdval hcval splitEvidence hcheck
                exact hfactor.trans hval.symm
              · simp [tamagawaExpected?, hs, hm, hc, hcheck] at h

/-- Every supported result, including a supplied tame type II terminal change,
is the intrinsic local Tamagawa number. -/
theorem tamagawaExpected_correct (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    [(e.baseChange ℚ).IsElliptic] {shift : Option TamagawaTypeIIIShift}
    {typeIV : Option TamagawaTypeIVEvidence} {typeII : Option TamagawaTypeIIShift}
    {splitting : Option TamagawaSplittingEvidence} {value : ℕ}
    (h : tamagawaExpected? e p shift typeIV typeII splitting = some value) :
    (e.baseChange ℚ).tamagawaNumberAt (rationalPlace p) = value := by
  cases typeII with
  | none =>
    exact tamagawaExpected_base_correct e p (by simpa [tamagawaExpected?] using h)
  | some shiftII =>
    cases shift with
    | some _ => simp [tamagawaExpected?] at h
    | none =>
      cases typeIV with
      | some _ => simp [tamagawaExpected?] at h
      | none =>
        cases splitting with
        | some _ => simp [tamagawaExpected?] at h
        | none =>
          by_cases hcheck : checkTameTypeII e p shiftII = true
          · rw [tamagawaExpected?, hcheck] at h
            cases h
            exact tamagawaNumberAt_eq_one_of_typeII_shift e p shiftII hcheck
          · simp [tamagawaExpected?, hcheck] at h

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
