/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Artifacts.Contracts

/-! A checked artifact paired with its pure mathematical contract. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- A checked artifact retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical contract. -/
  artifact : Artifact
  /-- Proof that its request and boxes satisfy the expected contract. -/
  contract : WitnessAccepts expected artifact

end VerifiedLcalc.Artifacts
