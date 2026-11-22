/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.Scan
public import VerifiedLcalc.Certificates.PrecisionPolicy
public import VerifiedLcalc.Certificates.WeierstrassInstances

/-! Raw request and artifact contracts for exact derivative certificates. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Normalization of the elliptic-curve L-function. -/
inductive Normalization
  | arithmetic
  | unitary
  deriving Repr, DecidableEq

/-- A demo target and an elliptic-curve target cannot share a certificate. -/
inductive Subject
  | monomial (degree : Nat)
  | ellipticCurve (equation : WeierstrassCurve ℤ) (normalization : Normalization)
  deriving Repr, DecidableEq

/-- Exact evaluation center determined by the subject and normalization. -/
def Subject.center : Subject → Rat
  | .monomial _ => 0
  | .ellipticCurve _ .arithmetic => 1
  | .ellipticCurve _ .unitary => 1 / 2

/-- The center implementation agrees with the documented case distinction. -/
theorem Subject.center_correct (s : Subject) :
    s.center = match s with
      | .monomial _ => 0
      | .ellipticCurve _ .arithmetic => 1
      | .ellipticCurve _ .unitary => 1 / 2 := by
  cases s with
  | monomial => rfl
  | ellipticCurve e n => cases n <;> rfl

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

/-- Mathematical acceptance contract. The finite rank is witnessed directly
by the supplied boxes, independently of the executable scan. -/
def WitnessAccepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.formatVersion = 1 ∧
  artifact.rank ≤ expected.settings.maxDerivative ∧
  artifact.derivativeBoxes.length = artifact.rank + 1 ∧
  Witness artifact.derivativeBoxes artifact.rank

/-- A checked artifact retains a proof of the pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical contract. -/
  artifact : Artifact
  /-- Proof that its request and boxes satisfy the expected contract. -/
  contract : WitnessAccepts expected artifact

end VerifiedLcalc.Artifacts
