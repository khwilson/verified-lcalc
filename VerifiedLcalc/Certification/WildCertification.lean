module
public import VerifiedLcalc.Certification.CentralCertification
public import VerifiedLcalc.Certification.NegativeSign
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic
@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

/-- Actual minimal-model coefficients, checked Tate transcripts, proved finite
products and the existing analytic enclosure together certify rank zero. -/
theorem certifyWildCentralModel (r : CentralResult)
    (hn : r.equation.Δ ≠ 0) (v : MinimalityWitness) (hv : v.Valid r.equation)
    (d : WildData) (hd : d.Valid r.equation)
    (hN : wildLevelFast r.equation d = r.conductor)
    (hw : wildSignFast r.equation d = r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  have hm : GloballyMinimalInput r.equation := minimal_of_witness r.equation v hv
  apply certifyMinimalCentralModel r hn hm
  · exact ((arithmeticModularWitness r.equation hn).wildLevel_eq hm d hd).trans
      ((wildLevel_eq_fast r.equation d).trans hN)
  · exact ((arithmeticModularWitness r.equation hn).wildSign_eq hm d hd).trans
      ((wildSign_eq_fast r.equation d hd).trans hw)
  · exact hp
  · exact hz

theorem central_zero_of_wild_negative (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (v : MinimalityWitness) (hv : v.Valid e)
    (d : WildData) (hd : d.Valid e) (hw : wildSignFast e d = -1) :
    (modularWitness e hn).formL 1 = 0 := by
  apply (modularWitness e hn).central_zero_of_negative_sign
  exact ((arithmeticModularWitness e hn).wildSign_eq (minimal_of_witness e v hv) d hd).trans
    ((wildSign_eq_fast e d hd).trans hw)

theorem rank_lower_bound_of_wild_negative (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (v : MinimalityWitness) (hv : v.Valid e)
    (d : WildData) (hd : d.Valid e) (hw : wildSignFast e d = -1) :
    1 ≤ analyticOrderAt (modularWitness e hn).formL (1 : ℂ) := by
  have hz := central_zero_of_wild_negative e hn v hv d hd hw
  have hne : analyticOrderAt (modularWitness e hn).formL (1 : ℂ) ≠ 0 :=
    ((modularWitness e hn).formL_differentiable.analyticAt 1).analyticOrderAt_ne_zero.mpr hz
  exact Order.one_le_iff_ne_zero.mpr hne
end VerifiedLcalc.Certification
