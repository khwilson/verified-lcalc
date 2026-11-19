module

public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open NumberField IsDedekindDomain

/-- The executable c6 invariant agrees with mathlib's invariant. -/
theorem modelC6_correct (e : (WeierstrassCurve ℤ)) :
    modelC6 e = e.c₆ := rfl

section Local
variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]

/-- A c4 valuation below four forbids a nonintegral change of scale. -/
theorem isMinimal_of_small_c4 (W : WeierstrassCurve K) [WeierstrassCurve.IsIntegral R W]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : v.Integers R)
    (hc : WithZero.exp (-4 : ℤ) < v W.c₄) : WeierstrassCurve.IsMinimal R W := by
  refine ⟨⟨by simpa using ‹WeierstrassCurve.IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe,
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W),
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : v (C • W).c₄ ≤ 1 := by
    rw [← WeierstrassCurve.integralModel_c₄_eq R (C • W)]
    exact hv.map_le_one _
  rw [WeierstrassCurve.variableChange_c₄, map_mul, map_pow] at hint
  have hinv : v ((C.u : K)⁻¹) ≤ 1 :=
    scale_bound _ _ 4 (by decide) hc (by simpa only [Units.val_inv_eq_inv_val] using hint)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hinv
  have hrv : valuation K (maximalIdeal R) ((C.u : K)⁻¹) ≤ 1 := by
    rw [← hr]
    exact valuation_le_one _ _
  simpa [WeierstrassCurve.variableChange_Δ, map_mul, map_pow] using
    mul_le_of_le_one_left' (pow_le_one' hrv 12)

/-- A c6 valuation below six forbids a nonintegral change of scale. -/
theorem isMinimal_of_small_c6 (W : WeierstrassCurve K) [WeierstrassCurve.IsIntegral R W]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : v.Integers R)
    (hc : WithZero.exp (-6 : ℤ) < v W.c₆) : WeierstrassCurve.IsMinimal R W := by
  refine ⟨⟨by simpa using ‹WeierstrassCurve.IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe,
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W),
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : v (C • W).c₆ ≤ 1 := by
    rw [← WeierstrassCurve.integralModel_c₆_eq R (C • W)]
    exact hv.map_le_one _
  rw [WeierstrassCurve.variableChange_c₆, map_mul, map_pow] at hint
  have hinv : v ((C.u : K)⁻¹) ≤ 1 :=
    scale_bound _ _ 6 (by decide) hc (by simpa only [Units.val_inv_eq_inv_val] using hint)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hinv
  have hrv : valuation K (maximalIdeal R) ((C.u : K)⁻¹) ≤ 1 := by
    rw [← hr]
    exact valuation_le_one _ _
  simpa [WeierstrassCurve.variableChange_Δ, map_mul, map_pow] using
    mul_le_of_le_one_left' (pow_le_one' hrv 12)
end Local

/-- Integer divisibility checks discharge the two invariant criteria at p. -/
theorem invariantMinimalAt_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (h : invariantMinimalAt e p = true) :
    WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ)) := by
  let v := rationalPlace p
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := (WeierstrassCurve.baseChange e R).baseChange K
  let : WeierstrassCurve.IsIntegral R W := ⟨⟨WeierstrassCurve.baseChange e R, rfl⟩⟩
  have h' : ¬ (p : Int)^4 ∣ modelC4 e ∨ ¬ (p : Int)^6 ∣ modelC6 e := by
    simpa only [invariantMinimalAt, decide_eq_true_eq, ne_eq, Int.dvd_iff_emod_eq_zero] using h
  rcases h' with h | h
  · apply isMinimal_of_small_c4 W Valued.v (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
    have he : W.c₄ = (modelC4 e : K) := by
      have hc : e.c₄ = modelC4 e := rfl
      simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, eq_intCast, hc, map_intCast]
    rw [he, completion_intCast_valuation]
    exact rationalPlace_intValuation_gt p 4 (modelC4 e) h
  · apply isMinimal_of_small_c6 W Valued.v (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
    have he : W.c₆ = (modelC6 e : K) := by
      have hc : e.c₆ = modelC6 e := rfl
      simp only [W, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆, eq_intCast, hc, map_intCast]
    rw [he, completion_intCast_valuation]
    exact rationalPlace_intValuation_gt p 6 (modelC6 e) h

end VerifiedLcalc.EllipticCurve
