module

public import VerifiedLcalc.Scan
public import VerifiedLcalc.Upstream.LedvinkaExponentialCore

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- An exact scalar coefficient times exp of an exact dyadic argument. -/
structure WeightedExpTerm where
  coefficient : Rat
  argument : Dyadic

/-- Multiply the exponential enclosure by a known coefficient. Negative
coefficients reverse which endpoint supplies the lower and upper bound. -/
def weightedExpBounds (term : WeightedExpTerm) (prec : Nat) : Rat × Rat :=
  let bounds := expBounds term.argument prec
  if 0 ≤ term.coefficient then
    (term.coefficient * bounds.1.toRat, term.coefficient * bounds.2.toRat)
  else (term.coefficient * bounds.2.toRat, term.coefficient * bounds.1.toRat)

/-- Bounds of a finite exponential sum, computed with exact rational addition. -/
def expSumBounds (prec : Nat) : List WeightedExpTerm → Rat × Rat
  | [] => (0, 0)
  | term :: terms =>
    let head := weightedExpBounds term prec
    let tail := expSumBounds prec terms
    (head.1 + tail.1, head.2 + tail.2)

/-- Add a separately certified absolute tail bound. The analytic proof layer
requires a proof of that tail estimate; the number is not trusted by itself. -/
def expSumBox (terms : List WeightedExpTerm) (prec : Nat) (tail : Rat) : Box :=
  let bounds := expSumBounds prec terms
  ⟨bounds.1 - tail, bounds.2 + tail, 0, 0⟩

end VerifiedLcalc.Numerics
