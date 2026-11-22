module

public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealization

/-! # Special-value certificate data

The catalogue value is input data. A special-value fact records an analytic
order and the normalized Taylor leading coefficient bound for every arithmetic
modular realization of the indexed curve.
-/

@[expose] public section

namespace VerifiedLcalc
open Modularity

/-- An exact rational interpretation of a reported Taylor leading coefficient
and its explicit absolute-error radius. -/
structure SpecialLValueClaim where
  /-- Decimal or rational value as reported by the input. -/
  reported : Rat
  /-- Explicit claimed maximum absolute error. -/
  error : Rat
  deriving Repr, DecidableEq

/-- A proved enclosure for the Taylor leading coefficient at the analytic
order of the actual curve L-function. -/
structure SpecialLValueFacts (curve : WeierstrassCurve ℤ) where
  /-- The order used to normalize the derivative by its factorial. -/
  order : Nat
  /-- The exact reported value and claimed error radius. -/
  claim : SpecialLValueClaim
  /-- The checked order and normalized leading coefficient bound for every
  arithmetic modular realization of this same curve. -/
  correct : ∀ m : ArithmeticModularRealization curve,
    analyticOrderAt m.formL 1 = order ∧
      |(iteratedDeriv order m.formL 1).re / (order.factorial : ℝ) -
        (claim.reported : ℝ)| ≤ (claim.error : ℝ)

end VerifiedLcalc
