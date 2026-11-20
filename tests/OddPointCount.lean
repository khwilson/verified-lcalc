import VerifiedLcalc.EllipticCurve.Correctness
import Lean

open VerifiedLcalc.EllipticCurve

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Exercise singular, ordinary and small-characteristic equations independently
-- of the analytic-rank certificates.
example : (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve (ZMod 3)).pointCountOddFinite = 4 := by
  decide +kernel
example : (⟨0, -1, 1, -10, -20⟩ : WeierstrassCurve (ZMod 5)).pointCountOddFinite = 5 := by
  decide +kernel
example : (⟨1, 2, 3, 4, 5⟩ : WeierstrassCurve (ZMod 7)).pointCountOddFinite =
    (⟨1, 2, 3, 4, 5⟩ : WeierstrassCurve (ZMod 7)).pointCountFinite := by decide +kernel

-- Zero, characteristic two, and composite moduli retain the general path.
example : computePointCount ⟨0, 0, 0, 0, 0⟩ 0 = 1 := by decide +kernel
example : computePointCount ⟨0, 0, 0, 0, 0⟩ 2 = 3 := by decide +kernel
example : computePointCount ⟨0, 0, 0, 0, 0⟩ 4 =
    (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve (ZMod 4)).pointCountFinite := by decide +kernel

open Lean Elab Command in
run_cmd do
  for name in [``WeierstrassCurve.squareRootCountOdd_correct,
      ``WeierstrassCurve.pointCountOddFinite_correct,
      ``computePointCount_eq_pointCountFinite,
      ``computePointCount_correct, ``computeFrobeniusTrace_correct] do
    let axioms ← liftTermElabM <| Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in fast point counting: {axiomName}"
