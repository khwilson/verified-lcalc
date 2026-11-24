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

/-! Compatibility imports for numerical-rank records. -/

@[expose] public section

/-- Compatibility name for the numerical-rank request representation. -/
abbrev instReprRequest_1 := VerifiedLcalc.NumericalRanks.instReprRequest

/-- Compatibility name for decidable equality of numerical-rank requests. -/
abbrev instDecidableEqRequest_1 := VerifiedLcalc.NumericalRanks.instDecidableEqRequest

/-- Compatibility name for the numerical-rank artifact representation. -/
abbrev instReprArtifact_1 := VerifiedLcalc.NumericalRanks.instReprArtifact

/-- Compatibility name for decidable equality of numerical-rank artifacts. -/
abbrev instDecidableEqArtifact_1 := VerifiedLcalc.NumericalRanks.instDecidableEqArtifact
