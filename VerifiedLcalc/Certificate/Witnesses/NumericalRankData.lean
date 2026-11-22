/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData

/-! Raw requests and observations for numerical small-derivative bounds. -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- Separate identity for threshold observations of raw iterated derivatives.
The policy fixes coordinatewise comparison and the half-bit cutoff rule. -/
structure Request where
  /-- Exact computation whose derivatives are classified. -/
  computation : Artifacts.Request
  /-- Precision policy that determines the cutoff. -/
  policy : PrecisionPolicy := globalPrecision

/-- Numerical lower bound `n` records boxes for derivatives 0 through n-1.
It makes no assertion of exact vanishing. -/
structure Artifact where
  /-- Numerical classification request answered by this artifact. -/
  request : Request
  /-- Number of consecutive derivative boxes claimed to lie within cutoff. -/
  numericalLowerBound : Nat
  /-- Supplied derivative enclosures in ascending order. -/
  derivativeBoxes : List Box

end VerifiedLcalc.NumericalRanks
