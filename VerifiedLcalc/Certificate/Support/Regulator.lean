/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic

/-! # Compatibility path for regulator facts -/

@[expose] public section

deriving instance Repr, DecidableEq for VerifiedLcalc.RegulatorClaim
