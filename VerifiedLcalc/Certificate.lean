/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Scan
public import VerifiedLcalc.Certificate.Artifacts.Data

/-! # Structural checks for numerical certificate artifacts -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Historical checker contract, stated by the finite scan equation. -/
def Accepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.formatVersion = 1 ∧
  artifact.rank ≤ expected.settings.maxDerivative ∧
  artifact.derivativeBoxes.length = artifact.rank + 1 ∧
  scan artifact.derivativeBoxes = some artifact.rank

instance (expected : Request) (artifact : Artifact) :
    Decidable (Accepts expected artifact) := by
  unfold Accepts
  infer_instance

theorem accepts_iff_witnessAccepts (expected : Request) (artifact : Artifact) :
    Accepts expected artifact ↔ WitnessAccepts expected artifact := by
  constructor
  · rintro ⟨hr, hf, hn, hl, hs⟩
    exact ⟨hr, hf, hn, hl, scan_correct _ _ hs⟩
  · rintro ⟨hr, hf, hn, hl, hs⟩
    exact ⟨hr, hf, hn, hl, witness_scan hs⟩

/-- Check identity, format, resource boundary, and the mathematical box witness. -/
def check (expected : Request) (artifact : Artifact) : Bool :=
  decide (Accepts expected artifact)

theorem check_correct (expected : Request) (artifact : Artifact) :
    check expected artifact = true ↔ Accepts expected artifact := by
  simp [check]

/-- There is no reuse across different exact requests, even when ranks agree. -/
theorem check_request_eq {expected : Request} {artifact : Artifact}
    (h : check expected artifact = true) : artifact.request = expected :=
  ((check_correct _ _).mp h).1

/-- Historical projection: the pure contract still implies a successful check. -/
theorem Checked.accepted {expected : Request} (c : Checked expected) :
    check expected c.artifact = true :=
  (check_correct _ _).mpr ((accepts_iff_witnessAccepts _ _).mpr c.contract)

/-- Recheck an artifact on retrieval; a cache miss or failed check is explicit. -/
def validate (expected : Request) (artifact : Artifact) : Option (Checked expected) :=
  if h : check expected artifact = true then
    some ⟨artifact, (accepts_iff_witnessAccepts _ _).mp ((check_correct _ _).mp h)⟩
  else none

theorem validate_correct {expected : Request} {artifact : Artifact} {c : Checked expected}
    (h : validate expected artifact = some c) :
    c.artifact = artifact ∧ Accepts expected artifact := by
  unfold validate at h
  split at h <;> rename_i hp
  · cases h
    exact ⟨rfl, (check_correct _ _).mp hp⟩
  · simp at h

end VerifiedLcalc.Artifacts
