/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.Certificate.Artifacts.Primitives
public import VerifiedLcalc.Certificate.Numerical.Precision

/-! # Numerical requests and recorded derivative boxes

* `Artifacts.Settings` records precision, term limit, and maximum derivative order.
  `Artifacts.BuildIdentity` identifies the toolchain, dependencies, and producer.
* `Artifacts.Request` identifies the subject and normalization, settings, build, and format.
  `Artifacts.Artifact` records its proposed exact order and derivative boxes for later checking.
* `NumericalRanks.Request` adds a cutoff policy to a computation request.
  `NumericalRanks.Artifact` records the derivative boxes and the proposed length of the
  initial segment within the cutoff.
-/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Resource choices for one computation request. -/
structure Settings where
  /-- Requested numerical precision in bits. -/
  precisionBits : Nat := globalPrecision.precisionBits
  /-- Maximum number of series terms in the request. -/
  termLimit : Nat
  /-- Largest requested derivative order. -/
  maxDerivative : Nat
  deriving Repr, DecidableEq

/-- Dependency identifiers supplied by the build. -/
structure BuildIdentity where
  /-- Lean toolchain identity supplied by the build. -/
  leanToolchain : String
  /-- Mathlib revision supplied by the build. -/
  mathlibRevision : String
  /-- Identifier for the numerical producer. -/
  producerRevision : String
  /-- Identifier for the certificate checker. -/
  checkerRevision : String
  deriving Repr, DecidableEq

/-- Complete structural identity for a future cache lookup. -/
structure Request where
  /-- Version of the certificate format. -/
  formatVersion : Nat
  /-- Mathematical object and normalization for the computation. -/
  subject : Subject
  /-- Numerical resource choices for the computation. -/
  settings : Settings
  /-- Dependency and tool identifiers for this request. -/
  build : BuildIdentity
  deriving Repr, DecidableEq

/-- Serializable evidence data. Its derivative boxes are untrusted until
matched by a finite witness and the analytic obligations. -/
structure Artifact where
  /-- Exact request this artifact answers. -/
  request : Request
  /-- Proposed vanishing order. -/
  rank : Nat
  /-- Supplied enclosures for derivatives in ascending order. -/
  derivativeBoxes : List Box
  deriving Repr, DecidableEq

end VerifiedLcalc.Artifacts

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

end VerifiedLcalc.NumericalRanks
