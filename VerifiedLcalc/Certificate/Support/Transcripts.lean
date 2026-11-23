/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Transcripts

/-! # Compatibility path for finite reduction transcripts -/

@[expose] public section

deriving instance Repr, DecidableEq for VerifiedLcalc.EllipticCurve.MinimalityWitness
deriving instance Repr, DecidableEq for VerifiedLcalc.EllipticCurve.TateWitness
deriving instance Repr, DecidableEq for VerifiedLcalc.EllipticCurve.WildData
