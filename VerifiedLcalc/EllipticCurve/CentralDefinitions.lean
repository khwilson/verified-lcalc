module

public import VerifiedLcalc.Certificates.NumericalData
public import VerifiedLcalc.Numerics.RationalExpCore

/-! Exact formula definitions used by central-value payload specifications.
Evaluator search and correctness theorems live in `CentralCore`. -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

/-- Lower rational endpoint of the fixed pi enclosure. -/
def piLower : Rat := 314159265358979323846 / 100000000000000000000
/-- Upper rational endpoint of the fixed pi enclosure. -/
def piUpper : Rat := 314159265358979323847 / 100000000000000000000

/-- Rational bounds for 2*pi/sqrt(N). Fixed 20-decimal pi bounds cap attainable
accuracy; the output interval records that error instead of hiding it. -/
def alphaBounds (conductor bits : Nat) : Rat × Rat :=
  let scale := 2 ^ bits
  let root := Nat.sqrt (conductor * scale ^ 2)
  (2 * piLower * scale / (root + 1 : Nat), 2 * piUpper * scale / root)

/-- Central-value summands: (1+w)*a_n/n * exp(-alpha*n). The index is stored
alongside each term so the semantic argument is unambiguous. -/
def centralTerms (coefficients : List Int) (rootNumber : Int) (alphaLo alphaHi : Rat) :
    List (Nat × RationalExpTerm) :=
  coefficients.zipIdx.map fun (a, j) =>
    (j + 1, ⟨((1 + rootNumber : Int) : Rat) * (a : Rat) / (j + 1 : Nat),
      -alphaHi * (j + 1 : Nat), -alphaLo * (j + 1 : Nat)⟩)

/-- Geometric ratio for the shifted square majorant. Past M,
((n+1)/n)^2 is at most ((M+2)/(M+1))^2. -/
def squareTailRatio (q : Rat) (limit : Nat) : Rat :=
  q * (((limit + 2 : Nat) : Rat) / (limit + 1 : Nat)) ^ 2

/-- Tail bound for sum_{n>M} n^2*q^n when the ratio test is strictly below 1. -/
def squareTailBound (q : Rat) (limit : Nat) : Option Rat :=
  let ratio := squareTailRatio q limit
  if 0 ≤ q ∧ ratio < 1 then
    some ((((limit + 1 : Nat) : Rat) ^ 2 * q ^ (limit + 1)) / (1 - ratio))
  else none

/-- Rectangle enclosing the truncated central sum and its symmetric tail. -/
def centralBox (coefficients : List Int) (rootNumber : Int) (alphaLo alphaHi : Rat)
    (prec : Nat) (tail : Rat) : Box :=
  let bounds := rationalExpSumBounds prec
    ((centralTerms coefficients rootNumber alphaLo alphaHi).map Prod.snd)
  ⟨bounds.1 - tail, bounds.2 + tail, 0, 0⟩

end VerifiedLcalc.EllipticCurve
