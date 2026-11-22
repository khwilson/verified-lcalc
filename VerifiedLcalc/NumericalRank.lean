module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.Certificates.NumericalRanks
public import VerifiedLcalc.Precision

/-! # Exact checks for numerical rank observations -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- Executable version of the mathematical contract, using Boolean cutoff checks. -/
def CheckAccepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.computation.formatVersion = 1 ∧
  2 ≤ expected.policy.precisionBits ∧
  expected.computation.settings.precisionBits = expected.policy.precisionBits ∧
  artifact.numericalLowerBound ≤ expected.computation.settings.maxDerivative + 1 ∧
  artifact.derivativeBoxes.length = artifact.numericalLowerBound ∧
  ∀ b ∈ artifact.derivativeBoxes, b.withinCutoff expected.policy.cutoff = true

instance (expected : Request) (artifact : Artifact) : Decidable (CheckAccepts expected artifact) := by
  unfold CheckAccepts
  infer_instance

theorem checkAccepts_iff_accepts (expected : Request) (artifact : Artifact) :
    CheckAccepts expected artifact ↔ Accepts expected artifact := by
  simp [CheckAccepts, Accepts, Box.withinCutoff_correct, Box.WithinCutoff]

/-- Check the request identity, resource bounds, and each derivative enclosure. -/
def check (expected : Request) (artifact : Artifact) : Bool :=
  decide (CheckAccepts expected artifact)

theorem check_correct (expected : Request) (artifact : Artifact) :
    check expected artifact = true ↔ Accepts expected artifact := by
  rw [← checkAccepts_iff_accepts]
  simp [check]

/-- A supplied request is retained exactly on success. -/
theorem check_request_eq {expected : Request} {artifact : Artifact}
    (h : check expected artifact = true) : artifact.request = expected :=
  ((check_correct _ _).mp h).1

/-- Historical projection: the pure contract still implies a successful check. -/
theorem Checked.accepted {expected : Request} (c : Checked expected) :
    check expected c.artifact = true := (check_correct _ _).mpr c.contract

/-- Return an observation together with evidence when its finite check passes. -/
def validate (expected : Request) (artifact : Artifact) : Option (Checked expected) :=
  if h : check expected artifact = true then
    some ⟨artifact, (check_correct _ _).mp h⟩
  else none

theorem validate_correct {expected : Request} {artifact : Artifact} {c : Checked expected}
    (h : validate expected artifact = some c) :
    c.artifact = artifact ∧ Accepts expected artifact := by
  unfold validate at h
  split at h <;> rename_i hp
  · cases h
    exact ⟨rfl, (check_correct _ _).mp hp⟩
  · simp at h

end VerifiedLcalc.NumericalRanks
