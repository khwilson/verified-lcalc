/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Artifacts.Primitives
public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Artifacts.Contracts
public import VerifiedLcalc.Certificate.Witnesses.Analytic
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! Compatibility imports for exact artifact records. -/

public section

export VerifiedLcalc.Artifacts (
  instReprSettings instDecidableEqSettings
  instReprNormalization instDecidableEqNormalization
  instReprSubject instDecidableEqSubject
  instReprBuildIdentity instDecidableEqBuildIdentity
  instReprRequest instDecidableEqRequest
  instReprArtifact instDecidableEqArtifact
)
