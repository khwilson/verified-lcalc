module

public import VerifiedLcalc.Scan
public import VerifiedLcalc.Certificates.Artifacts

/-! # Structural checks for numerical certificate artifacts -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Executable version of the pure contract, using the finite scan. -/
def ScanAccepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.formatVersion = 1 ∧
  artifact.rank ≤ expected.settings.maxDerivative ∧
  artifact.derivativeBoxes.length = artifact.rank + 1 ∧
  scan artifact.derivativeBoxes = some artifact.rank

instance (expected : Request) (artifact : Artifact) :
    Decidable (ScanAccepts expected artifact) := by
  unfold ScanAccepts
  infer_instance

theorem scanAccepts_iff_accepts (expected : Request) (artifact : Artifact) :
    ScanAccepts expected artifact ↔ Accepts expected artifact := by
  constructor
  · rintro ⟨hr, hf, hn, hl, hs⟩
    exact ⟨hr, hf, hn, hl, scan_correct _ _ hs⟩
  · rintro ⟨hr, hf, hn, hl, hs⟩
    exact ⟨hr, hf, hn, hl, witness_scan hs⟩

/-- Check identity, format, resource boundary, and the mathematical box witness. -/
def check (expected : Request) (artifact : Artifact) : Bool :=
  decide (ScanAccepts expected artifact)

theorem check_correct (expected : Request) (artifact : Artifact) :
    check expected artifact = true ↔ Accepts expected artifact := by
  rw [← scanAccepts_iff_accepts]
  simp [check]

/-- There is no reuse across different exact requests, even when ranks agree. -/
theorem check_request_eq {expected : Request} {artifact : Artifact}
    (h : check expected artifact = true) : artifact.request = expected :=
  ((check_correct _ _).mp h).1

/-- Historical projection: the pure contract still implies a successful check. -/
theorem Checked.accepted {expected : Request} (c : Checked expected) :
    check expected c.artifact = true := (check_correct _ _).mpr c.contract

/-- Recheck an artifact on retrieval; a cache miss or failed check is explicit. -/
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

end VerifiedLcalc.Artifacts
