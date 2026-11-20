module

public import VerifiedLcalc.EllipticCurve.Modularity.Fourier
public import VerifiedLcalc.Numerics.ExponentialIntegral
public import VerifiedLcalc.EllipticCurve.GlobalBounds

@[expose] public section
namespace VerifiedLcalc.Modularity
open MeasureTheory Set

/-- The central exponential formula follows by integrating the Fourier series.
The quantitative coefficient bound is a proof argument, not an axiom field. -/
theorem ModularRealization.central_exponential_hasSum {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e)
    (hb : ∀ n : ℕ, |(WeierstrassCurve.baseChange e ℚ).LFunction n| ≤ (n : ℤ) ^ 3) :
    HasSum (fun j : ℕ => (1 + (m.rootNumber : ℝ)) *
      ((WeierstrassCurve.baseChange e ℚ).LFunction (j + 1) : ℝ) / (j + 1 : ℕ) *
        Real.exp (-(2 * Real.pi / Real.sqrt m.level) * (j + 1 : ℕ)))
      (m.formL 1).re := by
  let a : ℝ := 2 * Real.pi / Real.sqrt m.level
  have ha : 0 < a := by
    apply div_pos (mul_pos (by norm_num) Real.pi_pos)
    exact Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)
  let b : ℕ → ℝ := fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j + 1)
  have hb' (j : ℕ) : |b j| ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := by
    dsimp [b]
    exact_mod_cast hb (j + 1)
  have hs := Numerics.hasSum_integral_exponential_series a ha b hb'
  have hv : (∫ t : ℝ in Ioi 1, ∑' j : ℕ, b j * Real.exp (-(a * (j + 1 : ℕ)) * t)) =
      ∫ t : ℝ in Ioi 1, (m.imaginaryFunction t).re := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have h := (m.imaginaryFunction_re_hasSum t (lt_trans (by norm_num) ht)).tsum_eq
    simpa only [b, a, neg_mul] using h
  have h := hs.mul_left (a * (1 + (m.rootNumber : ℝ)))
  rw [hv, ← m.central_re_integral] at h
  convert h using 1
  funext j
  dsimp [a, b]
  have hsqrt : Real.sqrt (m.level : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)).ne'
  field_simp

/-- The actual-curve coefficient bound is now proved from its Euler product;
no arithmetic compatibility argument is needed for the infinite tail. -/
theorem ModularRealization.central_exponential_hasSum_curve
    {e : (WeierstrassCurve ℤ)} (m : ModularRealization e) :
    HasSum (fun j : ℕ => (1 + (m.rootNumber : ℝ)) *
      ((WeierstrassCurve.baseChange e ℚ).LFunction (j + 1) : ℝ) / (j + 1 : ℕ) *
        Real.exp (-(2 * Real.pi / Real.sqrt m.level) * (j + 1 : ℕ)))
      (m.formL 1).re :=
  m.central_exponential_hasSum (EllipticCurve.LFunction_abs_le_cube _)

/-- Arithmetic prime-power identification and TauCeti multiplicativity discharge
the global bound needed by the central formula. -/
theorem ModularRealization.central_exponential_hasSum_of_primePowers
    {e : (WeierstrassCurve ℤ)} (m : ModularRealization e)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        EllipticCurve.computePrimePowerCoefficient e p k) :
    HasSum (fun j : ℕ => (1 + (m.rootNumber : ℝ)) *
      ((WeierstrassCurve.baseChange e ℚ).LFunction (j + 1) : ℝ) / (j + 1 : ℕ) *
        Real.exp (-(2 * Real.pi / Real.sqrt m.level) * (j + 1 : ℕ)))
      (m.formL 1).re :=
  m.central_exponential_hasSum (EllipticCurve.curveCoefficient_abs_le_cube e hl)

end VerifiedLcalc.Modularity
