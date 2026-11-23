/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Enclosures
public import VerifiedLcalc.Certificate.Witnesses.PrecisionPolicy
public import VerifiedLcalc.Certificate.Numerical.Precision
public import VerifiedLcalc.Certificate.Artifacts.Primitives
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! Raw exact request and artifact records. -/

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

/-- Serializable evidence data. Its derivative boxes are untrusted until
matched by a finite witness and the analytic obligations. -/
structure Artifact where
  /-- Exact request this artifact answers. -/
  request : Request
  /-- Proposed vanishing order. -/
  rank : Nat
  /-- Supplied enclosures for derivatives in ascending order. -/
  derivativeBoxes : List Box

end VerifiedLcalc.Artifacts
