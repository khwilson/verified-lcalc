/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Analytic.EvidencePredicates
public import VerifiedLcalc.Certificate.Analytic.EnclosurePredicates
public import VerifiedLcalc.EllipticCurve.Modularity.Canonical

/-! # Opt-in analytic evidence for the modularity assumption -/

@[expose] public section

namespace VerifiedLcalc.Certification

open Modularity EllipticCurve

/-- Opt-in elliptic evidence. The continuation comes from the modularity
assumption; actual derivative enclosures must still be proved by the backend. -/
structure AssumedExactEvidence (expected : Artifacts.Request) (artifact : Artifacts.Artifact) where
  /-- Integral equation whose modular realization interprets the checked artifact. -/
  equation : WeierstrassCurve ℤ
  /-- The equation is nonsingular. -/
  nonsingular : equation.Δ ≠ 0
  /-- The request names this curve with arithmetic normalization. -/
  subject : expected.subject = .ellipticCurve equation .arithmetic
  /-- The artifact boxes enclose derivatives of the modular L-function. -/
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k (modularWitness equation nonsingular).formL 1)

/-- Evidence interpreting finite numerical checks as enclosures of derivatives
of the L-function for an explicit arithmetic modular realization. -/
structure AssumedNumericalEvidence (expected : NumericalRanks.Request)
    (artifact : NumericalRanks.Artifact) where
  /-- Integral equation whose modular realization interprets the checked payload. -/
  equation : WeierstrassCurve ℤ
  /-- The equation is nonsingular. -/
  nonsingular : equation.Δ ≠ 0
  /-- The request names this curve with arithmetic normalization. -/
  subject : expected.computation.subject = .ellipticCurve equation .arithmetic
  /-- The artifact boxes enclose derivatives of the modular L-function. -/
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k (modularWitness equation nonsingular).formL 1)

end VerifiedLcalc.Certification

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
