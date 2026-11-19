import VerifiedLcalc.Upstream.LedvinkaExponentialCore

open Inclusion.IntervalDyadicReal

/-- Run the same proof-backed core without linking mathlib's analytic tree.
Input represents numerator * 2^(-exponent); output endpoints are exact rationals. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [numText, exponentText, precText] =>
    match numText.toInt?, exponentText.toInt?, precText.toNat? with
    | some num, some exponent, some prec =>
      let x := Dyadic.ofIntWithPrec num exponent
      let bounds := expBounds x prec
      IO.println s!"argument = {x.toRat}"
      IO.println s!"lower = {bounds.1.toRat}"
      IO.println s!"upper = {bounds.2.toRat}"
      return 0
    | _, _, _ =>
      IO.eprintln "Expected an integer numerator, integer exponent, and natural precision."
      return 2
  | _ =>
    IO.eprintln "Usage: lake exe exp-enclosure NUMERATOR EXPONENT PRECISION_BITS"
    return 2
