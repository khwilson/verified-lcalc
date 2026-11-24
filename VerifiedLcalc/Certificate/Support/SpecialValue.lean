/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Analytic

/-! # Compatibility path for special-value facts -/

public section

export VerifiedLcalc (
  instReprSpecialLValueClaim instDecidableEqSpecialLValueClaim
)
