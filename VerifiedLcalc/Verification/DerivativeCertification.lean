module
public import VerifiedLcalc.Verification.DerivativeEvaluator
public import VerifiedLcalc.Verification.WildCertification
@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

theorem certifyDerivativeModel (r : DerivativeResult)
    (hn : r.equation.Δ ≠ 0) (v : MinimalityWitness) (hv : v.Valid r.equation)
    (d : WildData) (hd : d.Valid r.equation)
    (hN : wildLevelFast r.equation d = r.conductor)
    (hw : wildSignFast r.equation d = -1)
    (hr : DerivativePayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 1 := by
  letI : (r.equation.baseChange ℚ).IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (r.equation.Δ : ℚ) ≠ 0 by exact_mod_cast hn)⟩
  have hm := minimal_of_witness r.equation v hv
  have hglobal := globalMinimal_of_witness r.equation v hv
  let m := modularWitness r.equation hn
  apply m.analyticOrder_one_of_derivativePayload r hr
  · exact (((arithmeticModularWitness r.equation hn).wildLevel_eq hglobal d hd).trans
      ((wildLevel_eq_fast r.equation d).trans hN)).symm
  · exact ((arithmeticModularWitness r.equation hn).wildSign_eq hglobal d hd).trans
      ((wildSign_eq_fast r.equation d hd).trans hw)
  · rw [hr.2.2.2.1]
    exact minimal_prefix r.equation hn hm r.termLimit
  · exact hz
end VerifiedLcalc.Certification
