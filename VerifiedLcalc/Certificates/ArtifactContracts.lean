/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificates.Scan

/-! Mathematical acceptance predicate for exact artifact data. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Mathematical acceptance contract. The finite rank is witnessed directly
by the supplied boxes, independently of the executable scan. -/
def WitnessAccepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.formatVersion = 1 ∧
  artifact.rank ≤ expected.settings.maxDerivative ∧
  artifact.derivativeBoxes.length = artifact.rank + 1 ∧
  Witness artifact.derivativeBoxes artifact.rank

end VerifiedLcalc.Artifacts
