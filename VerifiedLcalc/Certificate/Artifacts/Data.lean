/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Artifacts.Primitives
public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Artifacts.Contracts
public import VerifiedLcalc.Certificate.Witnesses.ArtifactChecked
public import VerifiedLcalc.Certificate.Support.WeierstrassInstances

/-! Compatibility imports and instances for exact artifact records. -/

@[expose] public section

deriving instance Repr for VerifiedLcalc.Artifacts.Settings
deriving instance DecidableEq for VerifiedLcalc.Artifacts.Settings
deriving instance Repr for VerifiedLcalc.Artifacts.Normalization
deriving instance DecidableEq for VerifiedLcalc.Artifacts.Normalization
deriving instance Repr for VerifiedLcalc.Artifacts.Subject
deriving instance DecidableEq for VerifiedLcalc.Artifacts.Subject
deriving instance Repr for VerifiedLcalc.Artifacts.BuildIdentity
deriving instance DecidableEq for VerifiedLcalc.Artifacts.BuildIdentity
deriving instance Repr for VerifiedLcalc.Artifacts.Request
deriving instance DecidableEq for VerifiedLcalc.Artifacts.Request
deriving instance Repr for VerifiedLcalc.Artifacts.Artifact
deriving instance DecidableEq for VerifiedLcalc.Artifacts.Artifact
