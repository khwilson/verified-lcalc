/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Regulator
public import VerifiedLcalc.Certificate.Witnesses.RegulatorClaim

/-! # Compatibility path for regulator facts -/

@[expose] public section

deriving instance Repr, DecidableEq for VerifiedLcalc.RegulatorClaim
