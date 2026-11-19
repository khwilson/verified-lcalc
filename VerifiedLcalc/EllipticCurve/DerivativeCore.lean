module
public import VerifiedLcalc.EllipticCurve.CentralCore
public import VerifiedLcalc.Numerics.RealIntervalCore
@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open Numerics

/-- Enclose log(t)*f(it/sqrt(N)) throughout one rational interval. -/
def derivativeCellBounds (cs : List Int) (al ah left right : Rat) (bits : Nat) : Option RealInterval := do
  let q := rationalExpBounds (-ah*right) (-al*left) bits
  let rem ← polynomialTailBound q.2 3 cs.length
  let poly := polynomialBounds bits q cs
  let partialSum := intervalMul q poly
  let f := (partialSum.1-rem,partialSum.2+rem)
  let logs := ((logBounds left 8 bits).1,(logBounds right 8 bits).2)
  return roundInterval bits (intervalMul ((right-left),(right-left)) (intervalMul logs f))

def derivativeFiniteBounds (cs : List Int) (al ah : Rat) (bits steps cutoff : Nat) : Option RealInterval := do
  let cells ← (List.range (steps*(cutoff-1))).mapM fun (j : Nat) =>
    derivativeCellBounds cs al ah (1+(j : Rat)/steps) (1+((j+1 : Nat) : Rat)/steps) bits
  return sumIntervalBounds bits cells

/-- The bound uses log(t)<=t and monotonicity of t*exp(-alpha*t/2)
for alpha*t>=2; the Fourier coefficient bound supplies 1/(1-8*q). -/
def derivativeInfiniteTail (al : Rat) (bits cutoff : Nat) : Option Rat :=
  let q := (rationalExpBounds (-al*cutoff) (-al*cutoff) bits).2
  if 0 < al ∧ 1 ≤ cutoff ∧ 2 ≤ al*cutoff ∧ 0 ≤ q ∧ 8*q < 1 then
    some (2*cutoff/al*q/(1-8*q))
  else none

structure DerivativeResult where
  equation : (WeierstrassCurve ℤ)
  conductor : Nat
  policy : PrecisionPolicy
  termLimit : Nat
  stepsPerUnit : Nat
  cutoff : Nat
  coefficients : List Int
  alphaLo : Rat
  alphaHi : Rat
  finite : RealInterval
  tail : Rat
  box : Box
  deriving Repr, DecidableEq

/-- Outward bounds for the real first derivative, obtained from the normalized
integral enclosure and the enclosing positive Mellin scale. -/
def DerivativeResult.realDerivativeBounds (r : DerivativeResult) : RealInterval :=
  intervalMul (2*r.alphaLo,2*r.alphaHi) (r.box.reLo,r.box.reHi)

/-- Enclosure of the normalized derivative integral J. The analytic bridge
proves Re L'(1)=(4*pi/sqrt(N))*J for the negative-sign realization. -/
def evaluateDerivative (equation : (WeierstrassCurve ℤ)) (conductor limit steps cutoff : Nat)
    (policy : PrecisionPolicy := globalPrecision) : Option DerivativeResult := do
  if conductor = 0 ∨ steps = 0 ∨ cutoff ≤ 1 then none else do
    let a := alphaBounds conductor policy.precisionBits
    let cs := modelCoefficients equation limit
    let tail ← derivativeInfiniteTail a.1 policy.precisionBits cutoff
    let finite ← derivativeFiniteBounds cs a.1 a.2 policy.precisionBits steps cutoff
    return ⟨equation,conductor,policy,limit,steps,cutoff,cs,a.1,a.2,finite,tail,
      ⟨finite.1-tail,finite.2+tail,0,0⟩⟩

/-- Finite contract; actual derivative interpretation is proved separately. -/
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

theorem evaluateDerivative_correct {e : (WeierstrassCurve ℤ)} {N M steps cutoff : Nat}
    {policy : PrecisionPolicy} {r : DerivativeResult}
    (h : evaluateDerivative e N M steps cutoff policy = some r) :
    r.equation = e ∧ r.conductor = N ∧ r.policy = policy ∧ r.termLimit = M ∧
      r.stepsPerUnit = steps ∧ r.cutoff = cutoff ∧ DerivativePayloadCorrect r := by
  unfold evaluateDerivative at h
  split at h
  · simp at h
  · next hn =>
    have hn' : 0 < N ∧ 0 < steps ∧ 1 < cutoff := by omega
    cases ht : derivativeInfiniteTail (alphaBounds N policy.precisionBits).1 policy.precisionBits cutoff with
    | none => simp [ht] at h
    | some tail =>
      cases hf : derivativeFiniteBounds (modelCoefficients e M)
          (alphaBounds N policy.precisionBits).1 (alphaBounds N policy.precisionBits).2
          policy.precisionBits steps cutoff with
      | none => simp [ht,hf] at h
      | some finite =>
        simp [ht,hf] at h
        cases h
        exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,hn'.1,hn'.2.1,hn'.2.2,rfl,rfl,rfl,ht,hf,rfl⟩
end VerifiedLcalc.EllipticCurve
