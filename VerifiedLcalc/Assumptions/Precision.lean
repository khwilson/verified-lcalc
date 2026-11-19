module

public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.NumericalRankSeparation

@[expose] public section

namespace VerifiedLcalc.Assumptions
open Modularity

/-- Identity of a proposed curve-specific numerical-to-exact upgrade.
The convention is fixed: raw iterated derivatives of the arithmetic L-function
at 1, coordinatewise cutoff, with no factorial or period normalization. -/
structure CurvePrecisionClaim where
  equation : (WeierstrassCurve ℤ)
  policy : PrecisionPolicy
  derivativeCount : Nat
  nonzeroGap : Rat
  deriving Repr, DecidableEq

/-- Explicit hypotheses associated with exactly one curve, derivative prefix,
precision policy and gap. Declaring a claim does not supply this proof.
Keep any assumed instance in a separate opt-in per-curve module. -/
structure CurvePrecisionClaim.Hypotheses (claim : CurvePrecisionClaim)
    (nonsingular : claim.equation.Δ ≠ 0) : Prop where
  cutoff_lt_gap : claim.policy.cutoff < claim.nonzeroGap
  separated : NumericalRanks.NonzeroDerivativeGap
    (modularWitness claim.equation nonsingular).formL 1
    claim.derivativeCount claim.nonzeroGap

end VerifiedLcalc.Assumptions
