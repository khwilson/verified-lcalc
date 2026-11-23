module

public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.EllipticCurve.Modularity.FastSign
public import VerifiedLcalc.EllipticCurve.Modularity.CentralIntegral
public import VerifiedLcalc.Analytic

@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve

/-- Convenience adapter from the verified semistable sign to the general
negative-root-number vanishing theorem. -/
theorem central_zero_of_semistable_negative (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (hs : SemistableModel e)
    (hw : semistableSignFast e = -1) :
    (modularWitness e hn).formL 1 = 0 :=
  (modularWitness e hn).central_zero_of_negative_sign
    (((modularWitness e hn).semistableSign_eq hs).trans ((semistableSign_eq_fast e).trans hw))

/-- This is a lower bound, not an exact rank-one assertion. -/
theorem rank_lower_bound_of_semistable_negative (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (hs : SemistableModel e)
    (hw : semistableSignFast e = -1) :
    1 ≤ analyticOrderAt (modularWitness e hn).formL (1 : ℂ) := by
  have hzero := central_zero_of_semistable_negative e hn hs hw
  have hne : analyticOrderAt (modularWitness e hn).formL (1 : ℂ) ≠ 0 :=
    ((modularWitness e hn).formL_differentiable.analyticAt 1).analyticOrderAt_ne_zero.mpr hzero
  exact Order.one_le_iff_ne_zero.mpr hne

end VerifiedLcalc.Certification
