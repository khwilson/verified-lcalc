/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealizationData
public import VerifiedLcalc.Certificate.Witnesses.SpecialValueClaim

/-! # Special-value claim and enclosure data

The facts use the existing mathematical arithmetic-realization type. This
type remains on its compatibility import path until its own lightweight
contract module is available.
-/

@[expose] public section

namespace VerifiedLcalc
open Modularity

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
