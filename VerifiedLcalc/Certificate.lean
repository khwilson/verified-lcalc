module

public import VerifiedLcalc.Scan
public import VerifiedLcalc.Precision
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! # Structural checks for numerical certificate artifacts -/

@[expose] public section

deriving instance Repr, DecidableEq for WeierstrassCurve

namespace VerifiedLcalc.Artifacts

/-- Normalization of the elliptic-curve L-function. -/
inductive Normalization
  | arithmetic
  | unitary
  deriving Repr, DecidableEq

/-- A demo target and a future elliptic-curve target cannot share a certificate. -/
inductive Subject
  | monomial (degree : Nat)
  | ellipticCurve (equation : (WeierstrassCurve ℤ)) (normalization : Normalization)
  deriving Repr, DecidableEq

/-- Exact evaluation center, determined by the subject rather than a label. -/
def Subject.center : Subject → Rat
  | .monomial _ => 0
  | .ellipticCurve _ .arithmetic => 1
  | .ellipticCurve _ .unitary => 1 / 2

theorem Subject.center_correct (s : Subject) :
    s.center = match s with
      | .monomial _ => 0
      | .ellipticCurve _ .arithmetic => 1
      | .ellipticCurve _ .unitary => 1 / 2 := by
  cases s with
  | monomial => rfl
  | ellipticCurve e n => cases n <;> rfl

/-- Resource choices are part of a computation request, not numerical theorems. -/
structure Settings where
  /-- Requested numerical precision in bits. -/
  precisionBits : Nat := globalPrecision.precisionBits
  /-- Maximum number of series terms in the request. -/
  termLimit : Nat
  /-- Largest requested derivative order. -/
  maxDerivative : Nat
  deriving Repr, DecidableEq

/-- Dependency identifiers must be supplied by the build. Equality of metadata
is not a proof that an artifact was built from these sources. -/
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

/-- Complete structural identity for future cache lookups. Hashing, storage, and
remote artifact authentication are deliberately outside this interface. -/
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

/-- Serializable evidence data. Enclosure proofs are supplied separately in the
analytic layer. Untrusted boxes by themselves never prove an analytic rank. -/
structure Artifact where
  /-- Exact request this artifact answers. -/
  request : Request
  /-- Proposed vanishing order. -/
  rank : Nat
  /-- Supplied enclosures for derivatives in ascending order. -/
  derivativeBoxes : List Box
  deriving Repr, DecidableEq

/-- Logical contract of the small checker. Only the r+1 necessary derivative
boxes are accepted; the numerical producer is never called during checking. -/
def Accepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.formatVersion = 1 ∧
  artifact.rank ≤ expected.settings.maxDerivative ∧
  artifact.derivativeBoxes.length = artifact.rank + 1 ∧
  scan artifact.derivativeBoxes = some artifact.rank

instance (expected : Request) (artifact : Artifact) : Decidable (Accepts expected artifact) := by
  unfold Accepts
  infer_instance

/-- Check identity, supported format, resource boundary, and the finite witness. -/
def check (expected : Request) (artifact : Artifact) : Bool :=
  decide (Accepts expected artifact)

theorem check_correct (expected : Request) (artifact : Artifact) :
    check expected artifact = true ↔ Accepts expected artifact := by
  simp [check]

/-- There is no reuse across different exact requests, even if their ranks agree. -/
theorem check_request_eq {expected : Request} {artifact : Artifact}
    (h : check expected artifact = true) : artifact.request = expected :=
  ((check_correct _ _).mp h).1

/-- A successful finite payload check. This is not yet an analytic certificate;
`CertificateSoundness` additionally requires proved analytic evidence. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the finite check. -/
  artifact : Artifact
  /-- Proof that the artifact passed the check against the expected request. -/
  accepted : check expected artifact = true

/-- Recheck an artifact on retrieval; a cache miss or failed check is explicit. -/
def validate (expected : Request) (artifact : Artifact) : Option (Checked expected) :=
  if h : check expected artifact = true then some ⟨artifact, h⟩ else none

theorem validate_correct {expected : Request} {artifact : Artifact} {c : Checked expected}
    (h : validate expected artifact = some c) :
    c.artifact = artifact ∧ Accepts expected artifact := by
  unfold validate at h
  split at h <;> rename_i hp
  · cases h
    exact ⟨rfl, (check_correct _ _).mp hp⟩
  · simp at h

end VerifiedLcalc.Artifacts
