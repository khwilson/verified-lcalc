module

public import VerifiedLcalc.Certificates.NumericalData
public import VerifiedLcalc.EllipticCurve.CentralDefinitions
public import VerifiedLcalc.Numerics.RealIntervalCore

/-! Exact quadrature and tail formulas used by derivative payload specifications.
Evaluator search and correctness theorems live in `DerivativeCore`. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

/-- Enclose log(t)*f(it/sqrt(N)) throughout one rational interval. -/
def derivativeCellBounds (cs : List Int) (al ah left right : Rat) (bits : Nat) :
    Option RealInterval := do
  let q := rationalExpBounds (-ah*right) (-al*left) bits
  let rem ← polynomialTailBound q.2 3 cs.length
  let poly := polynomialBounds bits q cs
  let partialSum := intervalMul q poly
  let f := (partialSum.1-rem,partialSum.2+rem)
  let logs := ((logBounds left 8 bits).1,(logBounds right 8 bits).2)
  return roundInterval bits (intervalMul ((right-left),(right-left)) (intervalMul logs f))

def derivativeFiniteBounds (cs : List Int) (al ah : Rat) (bits steps cutoff : Nat) :
    Option RealInterval := do
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

/-- Outward bounds for the real first derivative, obtained from the normalized
integral enclosure and the enclosing positive Mellin scale. -/
def DerivativeResult.realDerivativeBounds (r : DerivativeResult) : RealInterval :=
  intervalMul (2*r.alphaLo,2*r.alphaHi) (r.box.reLo,r.box.reHi)

end VerifiedLcalc.EllipticCurve
