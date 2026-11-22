/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.SpecialValue

/-! # Compatibility path for special-value facts -/

@[expose] public section

deriving instance Repr, DecidableEq for VerifiedLcalc.SpecialLValueClaim
