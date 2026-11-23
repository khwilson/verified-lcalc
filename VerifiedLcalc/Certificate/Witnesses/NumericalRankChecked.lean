/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.NumericalRankData
public import VerifiedLcalc.Certificate.Numerical.RankContracts

/-! A checked numerical observation paired with its cutoff contract. -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- A checked numerical observation retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical acceptance conditions. -/
  artifact : Artifact
  /-- Proof that request, bound, and boxes satisfy the expected conditions. -/
  contract : CutoffAccepts expected artifact

end VerifiedLcalc.NumericalRanks
