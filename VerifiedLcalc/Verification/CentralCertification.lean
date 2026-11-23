module

public import VerifiedLcalc.EllipticCurve.Modularity.Prefix
public import VerifiedLcalc.EllipticCurve.SemistableArithmetic
public import VerifiedLcalc.EllipticCurve.Tate.AdditiveArithmetic
public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.Verification.CentralEvaluator

/-!
# Central analytic certification

These theorems turn checked central-value evidence into vanishing of the
analytic order. The general-model result keeps the required level and sign
identities explicit; the semistable variants derive the coefficient prefix
from the corresponding arithmetic theorem.
-/

@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

/-- General minimal-model central certification, including additive primes.
The level and sign equalities remain explicit proof obligations: the current
modularity axiom does not identify them for additive curves. -/
theorem certifyMinimalCentralModel (r : CentralResult)
    (hn : r.equation.Δ ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((WeierstrassCurve.baseChange r.equation
          ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
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
    (hn : r.equation.Δ ≠ 0) (hs : SemistableModel r.equation)
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
    (hn : r.equation.Δ ≠ 0) (hs : SemistableModel r.equation)
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

end VerifiedLcalc.Certification
