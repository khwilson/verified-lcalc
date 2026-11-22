/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.NumericalRankData
public import VerifiedLcalc.Certificates.Artifacts
public import VerifiedLcalc.Certificates.NumericalRankContracts
public import VerifiedLcalc.Certificate.Witnesses.NumericalRankChecked

/-! Compatibility imports and instances for numerical-rank records. -/

@[expose] public section

deriving instance Repr for VerifiedLcalc.NumericalRanks.Request
deriving instance DecidableEq for VerifiedLcalc.NumericalRanks.Request
deriving instance Repr for VerifiedLcalc.NumericalRanks.Artifact
deriving instance DecidableEq for VerifiedLcalc.NumericalRanks.Artifact
