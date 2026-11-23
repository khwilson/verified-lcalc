/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic

/-! # Compatibility path and derived torsion projections -/

@[expose] public section

deriving instance Repr, DecidableEq for VerifiedLcalc.TorsionBoundWitness

namespace VerifiedLcalc

/-- The checked positive multiple of the full torsion order. -/
def TorsionDivisorFacts.bound {curve : WeierstrassCurve ℤ}
    (facts : TorsionDivisorFacts curve) : ℕ :=
  facts.evidence.bound

/-- The normalized invariant factors of a checked two-factor presentation. -/
def TwoFactorTorsionFacts.invariantFactors {curve : WeierstrassCurve ℤ}
    (facts : TwoFactorTorsionFacts curve) : List ℕ := [2, facts.secondOrder]

/-- The order of the full rational torsion subgroup in a two-factor presentation. -/
def TwoFactorTorsionFacts.order {curve : WeierstrassCurve ℤ}
    (facts : TwoFactorTorsionFacts curve) : ℕ := 2 * facts.secondOrder

end VerifiedLcalc
