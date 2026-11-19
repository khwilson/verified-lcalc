module

public import VerifiedLcalc.Assumptions.Batch
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic

@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

/-- Finite arithmetic facts specialize the authorized tame compatibility fields.
Neither N nor w is accepted without equality to the mathematical products. -/
theorem certifyTameCentralModel (r : CentralResult)
    (hn : discriminant r.equation ≠ 0) (v : MinimalityWitness)
    (hv : v.Valid r.equation) (ht : tameAtWild r.equation = true)
    (hN : tameLevelFast r.equation = r.conductor)
    (hw : tameSignFast r.equation = r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  have hm : GloballyMinimalInput r.equation := minimal_of_witness r.equation v hv
  apply certifyMinimalCentralModel r hn hm
  · exact ((arithmeticModularWitness r.equation hn).tameLevel_eq hm ht).trans
      ((tameLevel_eq_fast r.equation).trans hN)
  · exact ((arithmeticModularWitness r.equation hn).tameSign_eq hm ht).trans
      ((tameSign_eq_fast r.equation ht).trans hw)
  · exact hp
  · exact hz

end VerifiedLcalc.Assumptions
