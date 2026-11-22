module

public import VerifiedLcalc.Certificates.Enclosures
public import VerifiedLcalc.Upstream.LedvinkaExponentialCore

/-! # Exact rational enclosures for the exponential -/

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Outward rounding for a real argument between two exact rational endpoints.
Floor the lower endpoint and negate the floor of the negated upper endpoint. -/
def rationalExpBounds (lo hi : Rat) (prec : Nat) : Rat × Rat :=
  let lower := lo.toDyadic prec
  let upper := -((-hi).toDyadic prec)
  ((expBounds lower prec).1.toRat, (expBounds upper prec).2.toRat)

/-! Exact data for a rational multiple of an exponential term. -/
structure RationalExpTerm where
  /-- Rational multiplicative coefficient. -/
  coefficient : Rat
  /-- Lower endpoint for the exponential argument. -/
  argumentLo : Rat
  /-- Upper endpoint for the exponential argument. -/
  argumentHi : Rat
  deriving Repr, DecidableEq

/-- Enclose one weighted exponential term by outward-rounded rational bounds. -/
def rationalWeightedBounds (term : RationalExpTerm) (prec : Nat) : Rat × Rat :=
  let b := rationalExpBounds term.argumentLo term.argumentHi prec
  if 0 ≤ term.coefficient then (term.coefficient * b.1, term.coefficient * b.2)
  else (term.coefficient * b.2, term.coefficient * b.1)

/-- Add term enclosures without introducing floating point arithmetic. -/
def rationalExpSumBounds (prec : Nat) : List RationalExpTerm → Rat × Rat
  | [] => (0, 0)
  | term :: terms =>
    let head := rationalWeightedBounds term prec
    let rest := rationalExpSumBounds prec terms
    (head.1 + rest.1, head.2 + rest.2)

end VerifiedLcalc.Numerics
