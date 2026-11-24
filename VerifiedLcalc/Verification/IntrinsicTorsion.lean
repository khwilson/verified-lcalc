/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic

/-! # The intrinsic torsion subgroup when rational torsion is trivial

The intrinsic subgroup is the radical of the symmetric torsion pairing
defined by divisor evaluation. If the full rational torsion group has
order one, so does every subgroup, including that radical.
-/

public section

namespace VerifiedLcalc.IntrinsicTorsionFact

variable {curve : WeierstrassCurve ℤ}

/-- Every subgroup of the trivial rational torsion group has cardinality one. -/
theorem card_subgroup (fact : IntrinsicTorsionFact curve)
    (S : AddSubgroup (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point)) :
    Nat.card S = fact.reported := by
  let _ := (Nat.card_eq_one_iff_unique.mp fact.torsion_card).1
  exact Nat.card_unique.trans fact.reported_eq_one.symm

/-- In particular, any biadditive pairing on this rational torsion group
has a left radical of order one. -/
theorem card_radical (fact : IntrinsicTorsionFact curve) {A : Type*} [AddCommGroup A]
    (pairing : AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point →+
      (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point →+ A)) :
    Nat.card pairing.ker = fact.reported :=
  fact.card_subgroup pairing.ker

end VerifiedLcalc.IntrinsicTorsionFact
