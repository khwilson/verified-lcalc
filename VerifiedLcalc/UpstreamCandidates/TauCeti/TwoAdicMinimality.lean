module

public import VerifiedLcalc.UpstreamCandidates.TauCeti.Minimality
public import Mathlib.Tactic.Ring

@[expose] public section
namespace WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

private theorem valuation_le_uniformizer {x : WithZero (Multiplicative ℤ)}
    (hx : x ≤ 1) (hne : x ≠ 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hz : x = 0
  · simp [hz]
  rw [← WithZero.exp_log hz] at hx hne ⊢
  have hle : WithZero.log x ≤ 0 := by
    exact WithZero.exp_le_exp.mp (by simpa only [WithZero.exp_zero] using hx)
  have hne' : WithZero.log x ≠ 0 := by
    intro h
    exact hne (by simp only [h, WithZero.exp_zero])
  exact WithZero.exp_le_exp.mpr (by omega)

/-- In residue characteristic two an integral c4 is either a unit or divisible
by 16. This invariant obstruction detects models beyond the Delta<12 test. -/
theorem integral_c4_two_adic_gap {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : v.Integers R)
    (h2 : v (2 : K) = WithZero.exp (-1 : ℤ)) (W : WeierstrassCurve R) :
    v (algebraMap R K W.c₄) = 1 ∨
      v (algebraMap R K W.c₄) ≤ WithZero.exp (-4 : ℤ) := by
  by_cases ha : v (algebraMap R K W.a₁) = 1
  · left
    let t : R := 4 * W.a₁ ^ 2 * W.a₂ + 8 * W.a₂ ^ 2 - 24 * W.a₄ - 12 * W.a₁ * W.a₃
    have hc : W.c₄ = W.a₁ ^ 4 + 2 * t := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, t]
      ring
    have ht : v (algebraMap R K (2 * t)) < 1 := by
      rw [map_mul, map_ofNat, map_mul, h2]
      calc
        WithZero.exp (-1 : ℤ) * v (algebraMap R K t) ≤
            WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_of_nonneg_left (hv.map_le_one t) bot_le
        _ < 1 := by norm_num
    rw [hc, map_add]
    have hp : v (algebraMap R K (W.a₁ ^ 4)) = 1 := by rw [map_pow, map_pow, ha, one_pow]
    rw [v.map_add_eq_of_lt_left (by simpa only [hp] using ht), hp]
  · right
    have hdiv : (2 : R) ∣ W.a₁ := hv.dvd_of_le (by
      simpa only [map_ofNat, h2] using valuation_le_uniformizer (hv.map_le_one W.a₁) ha)
    obtain ⟨a, ha⟩ := hdiv
    have hc : W.c₄ = (2 : R) ^ 4 * ((a ^ 2 + W.a₂) ^ 2 - 3 * (W.a₄ + a * W.a₃)) := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, ha]
      ring
    rw [hc, map_mul, map_pow, map_ofNat, map_mul, map_pow, h2]
    calc
      WithZero.exp (-1 : ℤ) ^ 4 * v (algebraMap R K _) ≤ WithZero.exp (-1 : ℤ) ^ 4 * 1 :=
        mul_le_mul_of_nonneg_left (hv.map_le_one _) bot_le
      _ = WithZero.exp (-4 : ℤ) := by norm_num [← WithZero.exp_nsmul]

/-- A minimality criterion needed for the additive model 32.a4. An integral
change dividing c4 by a fourth power would force its valuation to be two,
which the preceding invariant identity excludes. -/
theorem isMinimal_of_two_adic_c4_six {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [WeierstrassCurve.IsIntegral R W]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : v.Integers R)
    (h2 : v (2 : K) = WithZero.exp (-1 : ℤ))
    (hc : v W.c₄ = WithZero.exp (-6 : ℤ)) : WeierstrassCurve.IsMinimal R W := by
  refine ⟨⟨by simpa using ‹WeierstrassCurve.IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe,
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W),
    WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W]
  have hscale : v ((C.u : K)⁻¹) ≤ 1 := by
    by_contra hgt
    have hgt : 1 < v ((C.u : K)⁻¹) := lt_of_not_ge hgt
    have hn : v ((C.u : K)⁻¹) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
    let k := WithZero.log (v ((C.u : K)⁻¹))
    have he : v ((C.u : K)⁻¹) = WithZero.exp k := (WithZero.exp_log hn).symm
    have hk : 0 < k := WithZero.exp_lt_exp.mp (by simpa only [WithZero.exp_zero, ← he] using hgt)
    have ht : v (C • W).c₄ = WithZero.exp (4 * k - 6) := by
      rw [WeierstrassCurve.variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, hc, he]
      rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
      congr 1
    have hle : 4 * k - 6 ≤ 0 := by
      apply WithZero.exp_le_exp.mp
      rw [← ht, WithZero.exp_zero, ← WeierstrassCurve.integralModel_c₄_eq R (C • W)]
      exact hv.map_le_one _
    have hk1 : k = 1 := by omega
    have hgap := integral_c4_two_adic_gap v hv h2 ((C • W).integralModel R)
    rw [WeierstrassCurve.integralModel_c₄_eq, ht, hk1] at hgap
    norm_num at hgap
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hscale
  have hrv : valuation K (maximalIdeal R) ((C.u : K)⁻¹) ≤ 1 := by
    rw [← hr]
    exact valuation_le_one _ _
  simpa [WeierstrassCurve.variableChange_Δ, map_mul, map_pow] using
    mul_le_of_le_one_left' (pow_le_one' hrv 12)

end WeierstrassCurve
