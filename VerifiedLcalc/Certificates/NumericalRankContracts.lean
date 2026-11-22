/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.NumericalRankData
public import VerifiedLcalc.Certificates.Enclosures

/-! Mathematical cutoff acceptance predicate for numerical observations. -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- Mathematical acceptance conditions for one numerical observation. -/
def CutoffAccepts (expected : Request) (artifact : Artifact) : Prop :=
  artifact.request = expected ∧
  expected.computation.formatVersion = 1 ∧
  2 ≤ expected.policy.precisionBits ∧
  expected.computation.settings.precisionBits = expected.policy.precisionBits ∧
  artifact.numericalLowerBound ≤ expected.computation.settings.maxDerivative + 1 ∧
  artifact.derivativeBoxes.length = artifact.numericalLowerBound ∧
  ∀ b ∈ artifact.derivativeBoxes, b.WithinCutoff expected.policy.cutoff

end VerifiedLcalc.NumericalRanks
