/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

/-! # Raw regulator claim input -/

@[expose] public section

namespace VerifiedLcalc

/-- A stored regulator decimal and optional explicit absolute-error evidence. -/
structure RegulatorClaim where
  /-- Exact rational interpretation of the stored decimal. -/
  reported : Rat
  /-- Explicit absolute error bound; absence means an exact-value claim. -/
  error : Option Rat := none

end VerifiedLcalc
