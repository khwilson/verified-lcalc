module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
namespace WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open scoped WithZero

/-- Discreteness of the value group bounds a change-of-variables scale. -/
private theorem scale_bound (a d : WithZero (Multiplicative ℤ)) (n : ℕ) (_hn : 0 < n)
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


section
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
end

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

end WeierstrassCurve
