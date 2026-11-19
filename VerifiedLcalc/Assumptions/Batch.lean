module

public import VerifiedLcalc.Assumptions.Prefix
public import VerifiedLcalc.EllipticCurve.SemistableArithmetic
public import VerifiedLcalc.EllipticCurve.AdditiveArithmetic
public import VerifiedLcalc.Assumptions.Modularity
public import VerifiedLcalc.Assumptions.CentralEvaluator

@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

/-- General minimal-model central certification, including additive primes.
The level and sign equalities remain explicit proof obligations: the current
modularity axiom does not identify them for additive curves. -/
theorem certifyMinimalCentralModel (r : CentralResult)
    (hn : discriminant r.equation ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((weierstrass r.equation ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
          ((rationalPlace p).adicCompletion ℚ)))
    (hN : (modularWitness r.equation hn).level = r.conductor)
    (hw : (modularWitness r.equation hn).rootNumber = r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  let m := modularWitness r.equation hn
  apply m.analyticOrder_zero_of_centralCoefficients r hp rfl hN.symm hw.symm
  · rw [hp.2.2.1]
    exact minimal_prefix r.equation hn hmin r.termLimit
  · exact hz

/-- Full semistable arithmetic engine. There is no prefix eligibility or
trace-size argument: all input-model Euler factors have been identified. -/
theorem certifySemistableCentralModel (r : CentralResult)
    (hn : discriminant r.equation ≠ 0) (hs : SemistableModel r.equation)
    (hN : semistableLevel r.equation = r.conductor)
    (hw : semistableSign r.equation = r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  let m := modularWitness r.equation hn
  apply m.analyticOrder_zero_of_centralCoefficients r hp rfl
    ((m.semistableLevel_eq hs).trans hN).symm
    ((m.semistableSign_eq hs).trans hw).symm
  · rw [hp.2.2.1]
    exact semistable_prefix r.equation hn hs r.termLimit
  · exact hz

/-- A batch certificate requires only finite checks. The uniform prefix
criterion supplies the actual coefficients; the existing central analysis
supplies the infinite series and its tail. All arithmetic identities in this
interface are proof inputs checked by Lean, never trusted metadata. -/
theorem certifySemistableCentral (r : CentralResult)
    (hn : discriminant r.equation ≠ 0) (hs : SemistableModel r.equation)
    (hN : semistableLevel r.equation = r.conductor)
    (hw : semistableSign r.equation = r.rootNumber)
    (hp : CentralPayloadCorrect r)
    (hc : prefixSupported r.equation r.termLimit = true)
    (hz : r.box.excludesZero = true) :
    analyticOrderAt (modularWitness r.equation hn).formL (1 : ℂ) = 0 := by
  let m := modularWitness r.equation hn
  apply m.analyticOrder_zero_of_centralCoefficients r hp rfl
    ((m.semistableLevel_eq hs).trans hN).symm
    ((m.semistableSign_eq hs).trans hw).symm
  · rw [hp.2.2.1]
    exact m.prefix_of_supported r.termLimit hc
  · exact hz

end VerifiedLcalc.Assumptions
