module

public import VerifiedLcalc.Scan
public import VerifiedLcalc.Upstream.LedvinkaExponentialCore

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Outward rounding for a real argument between two exact rational endpoints.
Floor the lower endpoint and negate the floor of the negated upper endpoint. -/
def rationalExpBounds (lo hi : Rat) (prec : Nat) : Rat × Rat :=
  let lower := lo.toDyadic prec
  let upper := -((-hi).toDyadic prec)
  ((expBounds lower prec).1.toRat, (expBounds upper prec).2.toRat)

structure RationalExpTerm where
  coefficient : Rat
  argumentLo : Rat
  argumentHi : Rat
  deriving Repr, DecidableEq

def rationalWeightedBounds (term : RationalExpTerm) (prec : Nat) : Rat × Rat :=
  let b := rationalExpBounds term.argumentLo term.argumentHi prec
  if 0 ≤ term.coefficient then (term.coefficient * b.1, term.coefficient * b.2)
  else (term.coefficient * b.2, term.coefficient * b.1)

def rationalExpSumBounds (prec : Nat) : List RationalExpTerm → Rat × Rat
  | [] => (0, 0)
  | term :: terms =>
    let head := rationalWeightedBounds term prec
    let rest := rationalExpSumBounds prec terms
    (head.1 + rest.1, head.2 + rest.2)

end VerifiedLcalc.Numerics
