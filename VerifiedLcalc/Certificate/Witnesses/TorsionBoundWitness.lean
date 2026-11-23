/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

/-! # Raw point-count torsion-bound input -/

@[expose] public section

namespace VerifiedLcalc

/-- Two proposed odd primes and the gcd of the corresponding finite-field point counts. -/
structure TorsionBoundWitness where
  /-- First proposed prime of good reduction. -/
  firstPrime : Nat
  /-- Second proposed prime of good reduction. -/
  secondPrime : Nat
  /-- Claimed positive gcd of the two reduced point counts. -/
  bound : Nat

end VerifiedLcalc
