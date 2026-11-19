module
public import VerifiedLcalc.Numerics.RationalExpCore
@[expose] public section
namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal
abbrev RealInterval := Rat × Rat

def roundInterval (bits : Nat) (i : RealInterval) : RealInterval :=
  ((i.1.toDyadic bits).toRat, -(((-i.2).toDyadic bits).toRat))
def intervalAdd (i j : RealInterval) : RealInterval := (i.1+j.1, i.2+j.2)
def intervalMul (i j : RealInterval) : RealInterval :=
  (min (min (i.1*j.1) (i.1*j.2)) (min (i.2*j.1) (i.2*j.2)),
   max (max (i.1*j.1) (i.1*j.2)) (max (i.2*j.1) (i.2*j.2)))

def polynomialBounds (bits : Nat) (q : RealInterval) : List Int → RealInterval
  | [] => (0,0)
  | a :: cs => roundInterval bits (intervalAdd ((a : Rat),(a : Rat))
      (intervalMul q (polynomialBounds bits q cs)))

def sumIntervalBounds (bits : Nat) : List RealInterval → RealInterval
  | [] => (0,0)
  | i :: is => roundInterval bits (intervalAdd i (sumIntervalBounds bits is))

def logBounds (t : Rat) (terms bits : Nat) : RealInterval :=
  let y := (t-1)/(t+1)
  let lo := 2*((List.range terms).map (fun k => y^(2*k+1)/(2*k+1 : Nat))).sum
  roundInterval bits (lo, lo+2*y^(2*terms+1)/(1-y^2))

def polynomialTailRatio (q : Rat) (power limit : Nat) : Rat :=
  q*((limit+2 : Rat)/(limit+1 : Rat))^power

def polynomialTailBound (q : Rat) (power limit : Nat) : Option Rat :=
  let ratio := polynomialTailRatio q power limit
  if 0 ≤ q ∧ ratio < 1 then some ((limit+1 : Rat)^power*q^(limit+1)/(1-ratio))
  else none
end VerifiedLcalc.Numerics
