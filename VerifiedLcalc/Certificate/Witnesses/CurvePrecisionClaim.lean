/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.PrecisionPolicy
public import VerifiedLcalc.Certificates.WeierstrassInstances

/-! Identity data for a curve-specific numerical-to-exact precision claim. -/

@[expose] public section

namespace VerifiedLcalc.Assumptions

/-- Identity of a proposed curve-specific numerical-to-exact upgrade.
The convention is fixed: raw iterated derivatives of the arithmetic L-function
at 1, coordinatewise cutoff, with no factorial or period normalization. -/
structure CurvePrecisionClaim where
  /-- Integral equation whose arithmetic L-function is under consideration. -/
  equation : WeierstrassCurve ℤ
  /-- Exact cutoff policy used for the derivative coordinates. -/
  policy : PrecisionPolicy
  /-- Number of consecutive derivatives classified by the claim. -/
  derivativeCount : Nat
  /-- Strict lower bound separating the first nonzero derivative from cutoff. -/
  nonzeroGap : Rat

end VerifiedLcalc.Assumptions
