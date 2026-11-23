/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.RealizationData
public import VerifiedLcalc.EllipticCurve.Correctness

/-! # Coefficients and analytic properties of a modular realization -/

@[expose] public section

namespace VerifiedLcalc.Modularity

open EllipticCurve

/-- Normalization follows from matching every actual curve coefficient; it is
not a separate field of the modularity assumption. -/
theorem ModularRealization.normalized {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) : (UpperHalfPlane.qExpansion 1 m.form).coeff 1 = 1 := by
  rw [m.coefficients, WeierstrassCurve.LFunction_apply_one]
  norm_num

/-- Numerical compatibility is derived from the canonical mathematical trace,
not supplied as an assumption about a particular evaluation algorithm. -/
theorem ModularRealization.goodPrimeCoefficients_computed {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (p : ℕ) (hp : p.Prime)
    (hg : goodReduction e p = true) :
    (UpperHalfPlane.qExpansion 1 m.form).coeff p = (computeFrobeniusTrace e p : ℂ) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := m.goodPrimeCoefficients p hp ((goodReduction_correct e p).mp hg)
  simpa only [← computeFrobeniusTrace_correct e p] using h

/-- Entirety for any supplied realization is already a mathlib theorem; no
modularity axiom is needed to prove this general implication. -/
theorem ModularRealization.formL_differentiable {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) : Differentiable ℂ m.formL := by
  let : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  exact CuspForm.differentiable_L (by decide : (0 : ℤ) < 2) m.form

/-- The supplied realization identifies the continued function with the actual
curve coefficient series on a convergence half-plane. No custom axiom occurs
in this implication: it works for any proved modular realization. -/
theorem ModularRealization.formL_hasSum {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) (s : ℂ) (hs : 2 < s.re) :
    HasSum (fun n : Nat => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ) / (n : ℂ) ^ s)
      (m.formL s) := by
  let : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  have h := CuspForm.hasSum_L (by decide : (0 : ℤ) < 2) m.form
    (by norm_num; exact hs)
  simpa [m.coefficients, ModularRealization.formL] using h

/-- Agreement with mathlib's named curve L-series where that series converges.
This equality is not asserted for the raw L-series definition at the center. -/
theorem ModularRealization.formL_eq_curveLSeries {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) (s : ℂ) (hs : 2 < s.re) :
    (WeierstrassCurve.baseChange equation ℚ).LSeries s = m.formL s := by
  change LSeries (fun n => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ)) s = m.formL s
  have hs0 : s ≠ 0 := by
    intro hz
    norm_num [hz] at hs
  have h := m.formL_hasSum s hs
  rw [← funext (LSeries.term_of_ne_zero' hs0
    (fun n => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ)))] at h
  exact LSeriesHasSum.LSeries_eq h

end VerifiedLcalc.Modularity
