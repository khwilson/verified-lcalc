/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.Certificate.Numerical.RankData
public import VerifiedLcalc.Precision

/-! # Exact checks for numerical rank observations -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- Historical checker contract, expressed through exact Boolean cutoff checks. -/
def Accepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.computation.formatVersion = 1 ∧
  2 ≤ expected.policy.precisionBits ∧
  expected.computation.settings.precisionBits = expected.policy.precisionBits ∧
  artifact.numericalLowerBound ≤ expected.computation.settings.maxDerivative + 1 ∧
  artifact.derivativeBoxes.length = artifact.numericalLowerBound ∧
  ∀ b ∈ artifact.derivativeBoxes, b.withinCutoff expected.policy.cutoff = true

instance (expected : Request) (artifact : Artifact) :
    Decidable (Accepts expected artifact) := by
  unfold Accepts
  infer_instance

theorem accepts_iff_cutoffAccepts (expected : Request) (artifact : Artifact) :
    Accepts expected artifact ↔ CutoffAccepts expected artifact := by
  simp [Accepts, CutoffAccepts, Box.withinCutoff_correct, Box.WithinCutoff]

/-- Check the request identity, resource bounds, and each derivative enclosure. -/
def check (expected : Request) (artifact : Artifact) : Bool :=
  decide (Accepts expected artifact)

theorem check_correct (expected : Request) (artifact : Artifact) :
    check expected artifact = true ↔ Accepts expected artifact := by simp [check]

/-- A supplied request is retained exactly on success. -/
theorem check_request_eq {expected : Request} {artifact : Artifact}
    (h : check expected artifact = true) : artifact.request = expected :=
  ((check_correct _ _).mp h).1

/-- Historical projection: the pure contract still implies a successful check. -/
theorem Checked.accepted {expected : Request} (c : Checked expected) :
    check expected c.artifact = true :=
  (check_correct _ _).mpr
    ((accepts_iff_cutoffAccepts _ _).mpr c.contract)

/-- Return an observation together with evidence when its finite check passes. -/
def validate (expected : Request) (artifact : Artifact) : Option (Checked expected) :=
  if h : check expected artifact = true then
    some ⟨artifact,
      (accepts_iff_cutoffAccepts _ _).mp ((check_correct _ _).mp h)⟩
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
