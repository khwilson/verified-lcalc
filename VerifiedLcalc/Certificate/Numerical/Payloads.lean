module

public import VerifiedLcalc.Certificate.Numerical.CoefficientDefinitions
public import VerifiedLcalc.Certificate.Numerical.Intervals
public import VerifiedLcalc.EllipticCurve.CentralDefinitions
public import VerifiedLcalc.EllipticCurve.DerivativeDefinitions

/-! Exact payload predicates that connect raw numerical records to their
specified coefficient and interval pipelines. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

/-- Complete finite contract of a successful central evaluator call. The
stored values cannot drift from the coefficient pipeline or policy. -/
def CentralPayloadCorrect (r : CentralResult) : Prop :=
  0 < r.conductor ∧ (r.rootNumber = 1 ∨ r.rootNumber = -1) ∧
  r.coefficients = modelCoefficients r.equation r.termLimit ∧
  r.alphaLo = (alphaBounds r.conductor r.policy.precisionBits).1 ∧
  r.alphaHi = (alphaBounds r.conductor r.policy.precisionBits).2 ∧
  r.geometricUpper =
    (rationalExpBounds (-r.alphaLo) (-r.alphaLo) r.policy.precisionBits).2 ∧
  ∃ remainder, squareTailBound r.geometricUpper r.termLimit = some remainder ∧
    r.tail = ((1 + r.rootNumber : Int).natAbs : Rat) * remainder ∧
    r.box = centralBox r.coefficients r.rootNumber r.alphaLo r.alphaHi
      r.policy.precisionBits r.tail

/-- Finite first-derivative contract; analytic interpretation is proved separately. -/
def DerivativePayloadCorrect (r : DerivativeResult) : Prop :=
  0 < r.conductor ∧ 0 < r.stepsPerUnit ∧ 1 < r.cutoff ∧
  r.coefficients = modelCoefficients r.equation r.termLimit ∧
  r.alphaLo = (alphaBounds r.conductor r.policy.precisionBits).1 ∧
  r.alphaHi = (alphaBounds r.conductor r.policy.precisionBits).2 ∧
  derivativeInfiniteTail r.alphaLo r.policy.precisionBits r.cutoff = some r.tail ∧
  derivativeFiniteBounds r.coefficients r.alphaLo r.alphaHi r.policy.precisionBits
    r.stepsPerUnit r.cutoff = some r.finite ∧
  r.box = ⟨r.finite.1-r.tail,r.finite.2+r.tail,0,0⟩
  deriving Decidable

end VerifiedLcalc.EllipticCurve
