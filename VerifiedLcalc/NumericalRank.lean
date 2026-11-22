module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.Precision

/-! # Exact checks for numerical rank observations -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- Separate identity for threshold observations of raw iterated derivatives.
Version 1 fixes coordinatewise comparison and the half-bit cutoff rule. -/
structure Request where
  /-- Exact computation whose derivatives are classified. -/
  computation : Artifacts.Request
  /-- Precision policy that determines the cutoff. -/
  policy : PrecisionPolicy := globalPrecision
  deriving Repr, DecidableEq

/-- `numericalLowerBound = n` means derivatives 0 through n-1 pass the
cutoff test. It does not assert that any of them is exactly zero. -/
structure Artifact where
  /-- Numerical classification request answered by this artifact. -/
  request : Request
  /-- Number of consecutive derivative boxes claimed to lie within the cutoff. -/
  numericalLowerBound : Nat
  /-- Supplied derivative enclosures in ascending order. -/
  derivativeBoxes : List Box
  deriving Repr, DecidableEq

/-- The structural and cutoff conditions for accepting a numerical observation. -/
def Accepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.computation.formatVersion = 1 ∧
  2 ≤ expected.policy.precisionBits ∧
  expected.computation.settings.precisionBits = expected.policy.precisionBits ∧
  artifact.numericalLowerBound ≤ expected.computation.settings.maxDerivative + 1 ∧
  artifact.derivativeBoxes.length = artifact.numericalLowerBound ∧
  ∀ b ∈ artifact.derivativeBoxes, b.withinCutoff expected.policy.cutoff = true

instance (expected : Request) (artifact : Artifact) : Decidable (Accepts expected artifact) := by
  unfold Accepts
  infer_instance

/-- Check the request identity, resource bounds, and every derivative enclosure. -/
def check (expected : Request) (artifact : Artifact) : Bool :=
  decide (Accepts expected artifact)

theorem check_correct (expected : Request) (artifact : Artifact) :
    check expected artifact = true ↔ Accepts expected artifact := by simp [check]

theorem check_request_eq {expected : Request} {artifact : Artifact}
    (h : check expected artifact = true) : artifact.request = expected :=
  ((check_correct _ _).mp h).1

/-- A numerical observation with a proof that its finite check passed. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the finite check. -/
  artifact : Artifact
  /-- Evidence that the artifact passed for the expected request. -/
  accepted : check expected artifact = true

/-- Return an observation together with evidence when its finite check passes. -/
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

end VerifiedLcalc.NumericalRanks
