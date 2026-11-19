module

public import VerifiedLcalc.Assumptions.Modularity
public import VerifiedLcalc.Assumptions.FastSign
public import VerifiedLcalc.Assumptions.CentralIntegral
public import VerifiedLcalc.Analytic

@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

/-- Negative sign forces an exact central zero, without derivative numerics. -/
theorem central_zero_of_semistable_negative (e : Artifacts.CurveEquation)
    (hn : discriminant e ≠ 0) (hs : SemistableModel e)
    (hw : semistableSignFast e = -1) :
    (modularWitness e hn).formL 1 = 0 := by
  let m := modularWitness e hn
  apply m.central_zero_of_negative_sign
  exact (m.semistableSign_eq hs).trans ((semistableSign_eq_fast e).trans hw)

/-- This is a lower bound, not an exact rank-one assertion. -/
theorem rank_lower_bound_of_semistable_negative (e : Artifacts.CurveEquation)
    (hn : discriminant e ≠ 0) (hs : SemistableModel e)
    (hw : semistableSignFast e = -1) :
    1 ≤ analyticOrderAt (modularWitness e hn).formL (1 : ℂ) := by
  have hzero := central_zero_of_semistable_negative e hn hs hw
  have hne : analyticOrderAt (modularWitness e hn).formL (1 : ℂ) ≠ 0 :=
    ((modularWitness e hn).formL_differentiable.analyticAt 1).analyticOrderAt_ne_zero.mpr hzero
  exact Order.one_le_iff_ne_zero.mpr hne

end VerifiedLcalc.Assumptions
