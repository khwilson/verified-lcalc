/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Assumptions

/-! Explicit curve-specific hypotheses for upgrading numerical smallness. -/

@[expose] public section

deriving instance Repr for VerifiedLcalc.Assumptions.CurvePrecisionClaim
deriving instance DecidableEq for VerifiedLcalc.Assumptions.CurvePrecisionClaim
