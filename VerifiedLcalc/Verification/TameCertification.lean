module

public import VerifiedLcalc.Verification.CentralCertification
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic

/-! # Analytic rank zero from a central enclosure and tame local data -/

@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

/-- Finite arithmetic facts specialize the authorized tame compatibility fields.
Neither N nor w is accepted without equality to the mathematical products. -/
theorem certifyTameCentralModel (r : CentralResult)
    (hn : r.equation.Δ ≠ 0) (v : MinimalityWitness)
    (hv : v.Valid r.equation) (ht : tameAtWild r.equation = true)
    (hN : tameLevelFast r.equation = r.conductor)
    (hw : tameSignFast r.equation = r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  let : (r.equation.baseChange ℚ).IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (r.equation.Δ : ℚ) ≠ 0 by exact_mod_cast hn)⟩
  have hm := minimal_of_witness r.equation v hv
  have hglobal := globalMinimal_of_witness r.equation v hv
  apply certifyMinimalCentralModel r hn hm
  · exact ((arithmeticModularWitness r.equation hn).tameLevel_eq hglobal ht).trans
      ((tameLevel_eq_fast r.equation).trans hN)
  · exact ((arithmeticModularWitness r.equation hn).tameSign_eq hglobal ht).trans
      ((tameSign_eq_fast r.equation ht).trans hw)
  · exact hp
  · exact hz

end VerifiedLcalc.Certification
