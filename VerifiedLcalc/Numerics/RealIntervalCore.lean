module
public import VerifiedLcalc.Upstream.LedvinkaExponentialCore
public import VerifiedLcalc.Certificate.Numerical.Intervals

/-! # Exact rational interval operations -/

@[expose] public section
namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal
/-- Round an interval outward to the requested dyadic grid. -/
def roundInterval (bits : Nat) (i : RealInterval) : RealInterval :=
  ((i.1.toDyadic bits).toRat, -(((-i.2).toDyadic bits).toRat))
/-- Add interval endpoints componentwise. -/
def intervalAdd (i j : RealInterval) : RealInterval := (i.1+j.1, i.2+j.2)
/-- Use endpoint signs to avoid computing products that cannot be extrema.
The mixed-sign fallback works without an ordering precondition; soundness only
requires that the input intervals contain their respective real arguments. -/
def intervalMul (i j : RealInterval) : RealInterval :=
  if 0 ≤ i.1 then
    if 0 ≤ j.1 then (i.1*j.1, i.2*j.2)
    else if j.2 ≤ 0 then (i.2*j.1, i.1*j.2)
    else (i.2*j.1, i.2*j.2)
  else if i.2 ≤ 0 then
    if 0 ≤ j.1 then (i.1*j.2, i.2*j.1)
    else if j.2 ≤ 0 then (i.2*j.2, i.1*j.1)
    else (i.1*j.2, i.1*j.1)
  else
    (min (min (i.1*j.1) (i.1*j.2)) (min (i.2*j.1) (i.2*j.2)),
     max (max (i.1*j.1) (i.1*j.2)) (max (i.2*j.1) (i.2*j.2)))

/-- Outward-rounded interval evaluation of an integer polynomial by Horner's rule. -/
def polynomialBounds (bits : Nat) (q : RealInterval) : List Int → RealInterval
  | [] => (0,0)
  | a :: cs => roundInterval bits (intervalAdd ((a : Rat),(a : Rat))
      (intervalMul q (polynomialBounds bits q cs)))

/-- Add a list of interval bounds with outward rounding at each step. -/
def sumIntervalBounds (bits : Nat) : List RealInterval → RealInterval
  | [] => (0,0)
  | i :: is => roundInterval bits (intervalAdd i (sumIntervalBounds bits is))

/-- Enclose `log t` using a finite atanh series and its geometric remainder. -/
def logBounds (t : Rat) (terms bits : Nat) : RealInterval :=
  let y := (t-1)/(t+1)
  let lo := 2*((List.range terms).map (fun k => y^(2*k+1)/(2*k+1 : Nat))).sum
  roundInterval bits (lo, lo+2*y^(2*terms+1)/(1-y^2))

/-- Ratio upper bound for consecutive terms in a polynomially weighted tail. -/
def polynomialTailRatio (q : Rat) (power limit : Nat) : Rat :=
  q*((limit+2 : Rat)/(limit+1 : Rat))^power

/-- Geometric majorant for the omitted polynomially weighted series tail. -/
def polynomialTailBound (q : Rat) (power limit : Nat) : Option Rat :=
  let ratio := polynomialTailRatio q power limit
  if 0 ≤ q ∧ ratio < 1 then some ((limit+1 : Rat)^power*q^(limit+1)/(1-ratio))
  else none
end VerifiedLcalc.Numerics
