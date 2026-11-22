/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

/-! Exact rational rectangle data stored in certificates. -/

@[expose] public section

namespace VerifiedLcalc

/-- Closed rational rectangle in the real and imaginary coordinates. -/
structure Box where
  /-- Lower real endpoint. -/
  reLo : Rat
  /-- Upper real endpoint. -/
  reHi : Rat
  /-- Lower imaginary endpoint. -/
  imLo : Rat
  /-- Upper imaginary endpoint. -/
  imHi : Rat

end VerifiedLcalc
