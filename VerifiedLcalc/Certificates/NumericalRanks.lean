/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.Artifacts

/-! Raw requests and mathematical acceptance contracts for numerical
small-derivative observations. -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- Separate identity for threshold observations of raw iterated derivatives.
The policy fixes coordinatewise comparison and the half-bit cutoff rule. -/
structure Request where
  /-- Exact computation whose derivatives are classified. -/
  computation : Artifacts.Request
  /-- Precision policy that determines the cutoff. -/
  policy : PrecisionPolicy := globalPrecision
  deriving Repr, DecidableEq

/-- Numerical lower bound `n` records boxes for derivatives 0 through n-1.
It makes no assertion of exact vanishing. -/
structure Artifact where
  /-- Numerical classification request answered by this artifact. -/
  request : Request
  /-- Number of consecutive derivative boxes claimed to lie within cutoff. -/
  numericalLowerBound : Nat
  /-- Supplied derivative enclosures in ascending order. -/
  derivativeBoxes : List Box
  deriving Repr, DecidableEq

/-- Mathematical acceptance conditions for one numerical observation. -/
def CutoffAccepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.computation.formatVersion = 1 ∧
  2 ≤ expected.policy.precisionBits ∧
  expected.computation.settings.precisionBits = expected.policy.precisionBits ∧
  artifact.numericalLowerBound ≤ expected.computation.settings.maxDerivative + 1 ∧
  artifact.derivativeBoxes.length = artifact.numericalLowerBound ∧
  ∀ b ∈ artifact.derivativeBoxes, b.WithinCutoff expected.policy.cutoff

/-- A checked numerical observation retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical acceptance conditions. -/
  artifact : Artifact
  /-- Proof that request, bound, and boxes satisfy the expected conditions. -/
  contract : CutoffAccepts expected artifact

end VerifiedLcalc.NumericalRanks
