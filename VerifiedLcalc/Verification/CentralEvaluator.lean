module

public import VerifiedLcalc.EllipticCurve.Modularity.CentralSeries
public import VerifiedLcalc.EllipticCurve.Central

/-! # Soundness of central-value enclosures for a modular realization -/

@[expose] public section
namespace VerifiedLcalc.Modularity
open EllipticCurve

/-- The stored geometric upper bound encloses the actual exponential ratio. -/
theorem centralPayload_exp_le {r : CentralResult} (h : CentralPayloadCorrect r) :
    Real.exp (-(2 * Real.pi / Real.sqrt r.conductor)) ≤ (r.geometricUpper : ℝ) := by
  obtain ⟨hn, _, _, hal, _, hq, _⟩ := h
  have ha := (alphaBounds_correct r.conductor r.policy.precisionBits hn).1
  rw [← hal] at ha
  have he := (Numerics.rationalExpBounds_correct (-r.alphaLo) (-r.alphaLo)
    r.policy.precisionBits (-(r.alphaLo : ℝ)) (by simp) (by simp)).2
  rw [hq]
  exact (Real.exp_le_exp.mpr (neg_le_neg ha)).trans he

/-- Assemble actual series, prefix identity and tail majorant. Only the finite
coefficient prefix needs identification; the actual global bound is proved. -/
noncomputable def ModularRealization.centralSeriesEvidence_of_coefficients
    {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (r : CentralResult) (hr : CentralPayloadCorrect r)
    (_he : r.equation = e) (hN : r.conductor = m.level) (hw : r.rootNumber = m.rootNumber)
    (hc : r.coefficients = (List.range r.termLimit).map
      (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j + 1))) :
    CentralSeriesEvidence r (m.formL 1).re := by
  let a : ℕ → ℤ := (WeierstrassCurve.baseChange e ℚ).LFunction
  let alpha : ℝ := 2 * Real.pi / Real.sqrt m.level
  refine {
    series := fun j => (1 + (m.rootNumber : ℝ)) * (a (j + 1) : ℝ) /
      (j + 1 : ℕ) * Real.exp (-alpha * (j + 1 : ℕ))
    formula := m.central_exponential_hasSum_curve
    finiteSum := ?_
    majorant := ?_
  }
  · rw [hc, centralFiniteValue_map_range, hN, hw]
    simp only [a, alpha, Int.cast_add, Int.cast_one]
  · intro j
    have hn : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hb : |(a (j + 1) : ℝ)| ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := by
      dsimp [a]
      exact_mod_cast LFunction_abs_le_cube (WeierstrassCurve.baseChange e ℚ) (j + 1)
    have hd : |(a (j + 1) : ℝ) / (j + 1 : ℕ)| ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [abs_div, abs_of_pos hn]
      apply (div_le_iff₀ hn).mpr
      nlinarith
    have hq : Real.exp (-alpha) ≤ (r.geometricUpper : ℝ) := by
      simpa only [alpha, hN] using centralPayload_exp_le hr
    have hpow : Real.exp (-alpha * (j + 1 : ℕ)) ≤ (r.geometricUpper : ℝ) ^ (j + 1) := by
      rw [show -alpha * (j + 1 : ℕ) = (j + 1 : ℕ) * (-alpha) by ring, Real.exp_natCast_mul]
      exact pow_le_pow_left₀ (Real.exp_nonneg _) hq _
    have habs : |1 + (m.rootNumber : ℝ)| = ((1 + r.rootNumber : ℤ).natAbs : ℝ) := by
      simp [hw]
    rw [show (1 + (m.rootNumber : ℝ)) * (a (j + 1) : ℝ) / (j + 1 : ℕ) *
      Real.exp (-alpha * (j + 1 : ℕ)) =
      (1 + (m.rootNumber : ℝ)) * ((a (j + 1) : ℝ) / (j + 1 : ℕ)) *
        Real.exp (-alpha * (j + 1 : ℕ)) by ring,
      abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), habs]
    calc
      _ ≤ ((1 + r.rootNumber : ℤ).natAbs : ℝ) *
          ((j + 1 : ℕ) : ℝ) ^ 2 * (r.geometricUpper : ℝ) ^ (j + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity)) hpow
          (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring

/-- Compatibility wrapper for the original prime-power proof interface. -/
noncomputable def ModularRealization.centralSeriesEvidence {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (r : CentralResult) (hr : CentralPayloadCorrect r)
    (he : r.equation = e) (hN : r.conductor = m.level) (hw : r.rootNumber = m.rootNumber)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        computePrimePowerCoefficient e p k) :
    CentralSeriesEvidence r (m.formL 1).re :=
  m.centralSeriesEvidence_of_coefficients r hr he hN hw (by
    rw [hr.2.2.1, he, modelCoefficients_eq_curve e hl])

/-- Complete central enclosure for any supplied modular realization and proved
prime-power identification. The numerical producer itself remains unchanged. -/
theorem ModularRealization.evaluateCentral_contains {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (limit : ℕ) (policy : PrecisionPolicy) (r : CentralResult)
    (hc : evaluateCentral e m.level m.rootNumber limit policy = some r)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        computePrimePowerCoefficient e p k) :
    r.box.Contains (Complex.ofReal (m.formL 1).re) := by
  obtain ⟨he, hN, hw, _, _, hr⟩ := evaluateCentral_correct hc
  exact centralPayload_sound hr (m.centralSeriesEvidence r hr he hN hw hl)

/-- Finite prefix identification suffices because the infinite actual-curve
coefficient bound is proved independently. -/
theorem ModularRealization.analyticOrder_zero_of_centralCoefficients
    {e : (WeierstrassCurve ℤ)} (m : ModularRealization e) (r : CentralResult)
    (hr : CentralPayloadCorrect r) (he : r.equation = e)
    (hN : r.conductor = m.level) (hw : r.rootNumber = m.rootNumber)
    (hc : r.coefficients = (List.range r.termLimit).map
      (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j + 1)))
    (hz : r.box.excludesZero = true) : analyticOrderAt m.formL (1 : ℂ) = 0 :=
  analyticOrder_zero_of_central (m.formL_differentiable.analyticAt 1) hr
    (m.centralSeriesEvidence_of_coefficients r hr he hN hw hc) hz

/-- A separated central payload gives exact analytic order zero once the
arithmetic prime-power bridge is proved. -/
theorem ModularRealization.analyticOrder_zero_of_centralPayload
    {e : (WeierstrassCurve ℤ)} (m : ModularRealization e) (r : CentralResult)
    (hr : CentralPayloadCorrect r) (he : r.equation = e)
    (hN : r.conductor = m.level) (hw : r.rootNumber = m.rootNumber)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        computePrimePowerCoefficient e p k)
    (hz : r.box.excludesZero = true) : analyticOrderAt m.formL (1 : ℂ) = 0 :=
  analyticOrder_zero_of_central (m.formL_differentiable.analyticAt 1) hr
    (m.centralSeriesEvidence r hr he hN hw hl) hz

end VerifiedLcalc.Modularity
