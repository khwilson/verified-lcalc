import VerifiedLcalc.EllipticCurve.TorsionStructure
import Lean

/-! Regression tests for cyclic torsion recovery from exact order and a cardinality divisor. -/

open Lean Elab Command VerifiedLcalc.EllipticCurve

example : ∃ e : ZMod 6 ≃+ AddCommGroup.torsion (ZMod 6), (e 1 : ZMod 6) = 1 := by
  apply exists_torsion_addEquiv_of_order_dvd (by decide) (ZMod.addOrderOf_one 6)
  exact (AddCommGroup.torsion (ZMod 6)).card_addSubgroup_dvd_card.trans
    (Nat.card_zmod 6).dvd

-- The additive group of integers has trivial torsion, witnessed by its identity.
example : Nat.card (AddCommGroup.torsion ℤ) = 1 := by
  apply torsion_card_eq_of_order_dvd (P := (0 : ℤ)) (by decide) addOrderOf_zero
  have htrivial : AddCommGroup.torsion ℤ = ⊥ := AddCommGroup.isAddTorsionFree_iff_torsion_eq_bot.mp
    inferInstance
  simp [htrivial]

run_cmd do
  for name in [``torsion_card_eq_of_order_dvd, ``exists_torsion_addEquiv_of_order_dvd] do
    for ax in ← liftTermElabM <| Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected cyclic torsion theorem axiom: {ax}"
