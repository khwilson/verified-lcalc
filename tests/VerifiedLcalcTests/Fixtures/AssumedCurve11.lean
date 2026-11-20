module

public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.EllipticCurve.Modularity.FastSign
public import VerifiedLcalc.EllipticCurve.Modularity.CentralIntegral
public import VerifiedLcalcTests.Arithmetic.Examples

@[expose] public section
open VerifiedLcalc

namespace VerifiedLcalcTests.Fixtures.AssumedCurve11

open Modularity EllipticCurve

/-- CONDITIONAL certificate: this realization depends on the named temporary
modularity axiom. It is not an unconditional elliptic analytic-rank result. -/
noncomputable def realization : ModularRealization Examples.curve11 :=
  modularWitness Examples.curve11 (by decide)

noncomputable def continuedL : ℂ → ℂ := realization.formL

theorem semistable : SemistableModel Examples.curve11 := by decide +kernel

theorem arithmetic_level : semistableLevel Examples.curve11 = 11 := by decide +kernel

theorem arithmetic_sign : semistableSign Examples.curve11 = 1 := by
  rw [semistableSign_eq_fast]
  decide +kernel

theorem realization_level : realization.level = 11 :=
  (realization.semistableLevel_eq semistable).trans arithmetic_level

theorem realization_sign : realization.rootNumber = 1 :=
  (realization.semistableSign_eq semistable).trans arithmetic_sign

/-- The central integral now has the computed conductor and sign. This is an
analytic identity, not yet an exponential-series numerical enclosure. -/
theorem continuedL_central_integral :
    continuedL 1 = (2 * Real.pi / Real.sqrt 11 : ℂ) * 2 *
      mellin ((Set.Ioi (1 : ℝ)).indicator realization.imaginaryFunction) 1 := by
  have h := realization.central_upper_mellin
  norm_num [continuedL, realization_level, realization_sign] at h ⊢
  exact h

theorem continuedL_entire : Differentiable ℂ continuedL :=
  realization.formL_differentiable

/-- The series here uses mathlib's actual curve Euler coefficients. The axiom
is visible under `#print axioms`; no small numerical values are declared zero. -/
theorem continuedL_matches_euler_series (s : ℂ) (hs : 2 < s.re) :
    HasSum (fun n : Nat => ((WeierstrassCurve.baseChange Examples.curve11 ℚ).LFunction n : ℂ) /
      (n : ℂ) ^ s) (continuedL s) :=
  realization.formL_hasSum s hs

theorem continuedL_agrees_with_curveLSeries (s : ℂ) (hs : 2 < s.re) :
    (WeierstrassCurve.baseChange Examples.curve11 ℚ).LSeries s = continuedL s :=
  realization.formL_eq_curveLSeries s hs

theorem form_coefficient_two :
    (UpperHalfPlane.qExpansion 1 realization.form).coeff 2 = (-2 : ℂ) := by
  have h := realization.goodPrimeCoefficients_computed 2 (by decide) (by decide)
  have htrace : computeFrobeniusTrace Examples.curve11 2 = -2 := by decide
  simpa only [htrace, Int.cast_neg, Int.cast_ofNat] using h

end VerifiedLcalcTests.Fixtures.AssumedCurve11
