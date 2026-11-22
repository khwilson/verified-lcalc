/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

/-! Immutable precision configuration recorded with certificate evidence. -/

@[expose] public section

namespace VerifiedLcalc

/-- Immutable precision settings recorded in numerical evidence. -/
structure PrecisionPolicy where
  /-- Number of binary precision bits requested by the exact evaluator. -/
  precisionBits : Nat

end VerifiedLcalc
