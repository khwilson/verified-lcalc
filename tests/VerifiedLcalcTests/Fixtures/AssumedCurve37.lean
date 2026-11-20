module

public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.EllipticCurve.Modularity.FastSign
public import VerifiedLcalc.EllipticCurve.Modularity.CentralIntegral
public import VerifiedLcalc.Analytic

@[expose] public section
open VerifiedLcalc

namespace VerifiedLcalcTests.Fixtures.AssumedCurve37
open Modularity EllipticCurve

/-- The integral model of 37.a1. No reference rank is an input. -/
def equation : (WeierstrassCurve ℤ) := ⟨0, 0, 1, -1, 0⟩

theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel

theorem semistable : SemistableModel equation := by decide +kernel

theorem arithmetic_level : semistableLevel equation = 37 := by decide +kernel

theorem arithmetic_sign : semistableSign equation = -1 := by
  rw [semistableSign_eq_fast]
  decide +kernel

/-- This choice, and the results about it, depend on ellipticModularity. -/
noncomputable def realization : ModularRealization equation :=
  modularWitness equation nonsingular

noncomputable def continuedL : ℂ → ℂ := realization.formL

theorem realization_level : realization.level = 37 :=
  (realization.semistableLevel_eq semistable).trans arithmetic_level

theorem realization_sign : realization.rootNumber = -1 :=
  (realization.semistableSign_eq semistable).trans arithmetic_sign

theorem continuedL_entire : Differentiable ℂ continuedL :=
  realization.formL_differentiable

/-- Exact vanishing from the proved odd-sign Mellin identity. No floating-point
calculation, numerical cutoff, or reference rank is used. -/
theorem central_vanishing : continuedL 1 = 0 :=
  realization.central_zero_of_negative_sign realization_sign

/-- An actual conditional analytic-rank lower bound. This does not assert that
the first derivative is nonzero, so it does not assert exact rank one. -/
theorem analytic_rank_at_least_one : 1 ≤ analyticOrderAt continuedL (1 : ℂ) := by
  have hne : analyticOrderAt continuedL (1 : ℂ) ≠ 0 :=
    (continuedL_entire.analyticAt 1).analyticOrderAt_ne_zero.mpr central_vanishing
  exact Order.one_le_iff_ne_zero.mpr hne

end VerifiedLcalcTests.Fixtures.AssumedCurve37
