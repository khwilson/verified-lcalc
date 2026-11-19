module
public import VerifiedLcalc.Assumptions.DerivativeEvaluator
public import VerifiedLcalc.Assumptions.WildCertification
@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

theorem certifyDerivativeModel (r : DerivativeResult)
    (hn : discriminant r.equation ≠ 0) (v : MinimalityWitness) (hv : v.Valid r.equation)
    (d : WildData) (hd : d.Valid r.equation)
    (hN : wildLevelFast r.equation d = r.conductor)
    (hw : wildSignFast r.equation d = -1)
    (hr : DerivativePayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 1 := by
  have hm : GloballyMinimalInput r.equation := minimal_of_witness r.equation v hv
  let m := modularWitness r.equation hn
  apply m.analyticOrder_one_of_derivativePayload r hr
  · exact (((arithmeticModularWitness r.equation hn).wildLevel_eq hm d hd).trans
      ((wildLevel_eq_fast r.equation d).trans hN)).symm
  · exact ((arithmeticModularWitness r.equation hn).wildSign_eq hm d hd).trans
      ((wildSign_eq_fast r.equation d hd).trans hw)
  · rw [hr.2.2.2.1]
    exact minimal_prefix r.equation hn hm r.termLimit
  · exact hz
end VerifiedLcalc.Assumptions
