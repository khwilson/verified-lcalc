/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Artifacts.Data
public import VerifiedLcalc.Certificate.Numerical.RankContracts
public import VerifiedLcalc.Certificate.Witnesses.Analytic

/-! Compatibility imports and instances for numerical-rank records. -/

@[expose] public section

deriving instance Repr for VerifiedLcalc.NumericalRanks.Request
deriving instance DecidableEq for VerifiedLcalc.NumericalRanks.Request
deriving instance Repr for VerifiedLcalc.NumericalRanks.Artifact
deriving instance DecidableEq for VerifiedLcalc.NumericalRanks.Artifact
