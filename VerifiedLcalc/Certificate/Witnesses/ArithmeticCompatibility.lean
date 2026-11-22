/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.Realization

/-! Conductor and root-number compatibility witness data. -/

@[expose] public section

namespace VerifiedLcalc.Certification
open VerifiedLcalc.Modularity

/-- Proof-carrying conductor/sign compatibility for a modular realization. -/
structure ArithmeticCompatibility (e : WeierstrassCurve ℤ) (N : Nat) (w : Int) where
  /-- Modular realization whose arithmetic data is being matched. -/
  realization : ModularRealization e
  /-- The realization has the supplied conductor. -/
  conductor_eq : realization.level = N
  /-- The realization has the supplied root number. -/
  rootNumber_eq : realization.rootNumber = w

end VerifiedLcalc.Certification
