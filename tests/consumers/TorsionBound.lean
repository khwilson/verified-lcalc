import VerifiedLcalcTests.Arithmetic.TorsionBound

/-! # Reuse the compiled rational torsion calculation -/

open Lean Elab Command
open TauCeti.WorkedExamples (curve37a1)

example : Nat.card (AddCommGroup.torsion (curve37a1.baseChange ℚ).toAffine.Point) = 1 :=
  VerifiedLcalcTests.TorsionBound.card_torsion_curve37a1

run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← liftTermElabM <|
    Lean.collectAxioms ``VerifiedLcalcTests.TorsionBound.card_torsion_curve37a1
  for axiomName in axioms do
    unless standard.contains axiomName do
      throwError "Unexpected rational torsion axiom {axiomName}"
