/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Numerical.Intervals
public import VerifiedLcalc.Upstream.LedvinkaExponentialCore

/-! # Exact rational enclosures for the exponential -/

@[expose] public section

namespace VerifiedLcalc.Numerics
open Inclusion.IntervalDyadicReal

/-- Outward dyadic bounds for the exponential on an interval with rational endpoints.
Floor the lower argument and negate the floor of the negated upper argument. -/
def rationalExpDyadicBounds (lo hi : Rat) (prec : Nat) : Dyadic × Dyadic :=
  let lower := lo.toDyadic prec
  let upper := -((-hi).toDyadic prec)
  ((expBounds lower prec).1, (expBounds upper prec).2)

/-- Rational endpoints of the outward dyadic enclosure of the exponential. -/
def rationalExpBounds (lo hi : Rat) (prec : Nat) : Rat × Rat :=
  Prod.map Dyadic.toRat Dyadic.toRat (rationalExpDyadicBounds lo hi prec)

/-- Exact data for a rational multiple of an exponential term. -/
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
