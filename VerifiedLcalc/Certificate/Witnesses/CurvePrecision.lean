/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.CurvePrecisionClaim
public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.Certificate.Analytic.EvidencePredicates
public import VerifiedLcalc.Certificate.Numerical.Precision

/-! Explicit opt-in hypotheses for one curve-specific precision claim. -/

@[expose] public section

namespace VerifiedLcalc.Assumptions
open Modularity

/-- Explicit hypotheses associated with exactly one curve, derivative prefix,
precision policy and gap. Declaring a claim does not supply this proof. -/
structure CurvePrecisionClaim.Hypotheses (claim : CurvePrecisionClaim)
    (nonsingular : claim.equation.Δ ≠ 0) : Prop where
  /-- The stated nonzero gap is larger than the numerical cutoff. -/
  cutoff_lt_gap : claim.policy.cutoff < claim.nonzeroGap
  /-- Every derivative in the certified prefix is separated from zero. -/
  separated : NumericalRanks.NonzeroDerivativeGap
    (modularWitness claim.equation nonsingular).formL 1
    claim.derivativeCount claim.nonzeroGap

end VerifiedLcalc.Assumptions
