import CertifiedCurves.Data

-- Import and use the compiled arithmetic theorems without reading witness JSON.
theorem imported_ap_bad_prime : (Data37.curve.baseChange ℚ).LFunction 37 = -1 :=
  Data37.ap_correct 37 (-1) (by decide +kernel)

theorem imported_integral_point :
    Data37.point ⟨8, by decide⟩ ∈ Data37.curve.integralPoints :=
  Data37.point_integral _

#print axioms imported_ap_bad_prime
#print axioms imported_integral_point

/-- The compiled certificate proves trivial rational torsion for 37.a1. -/
theorem imported_torsion_order :
    Nat.card (AddCommGroup.torsion (Data37.curve.baseChange ℚ).toAffine.Point) = 1 :=
  Data37.torsion

open Lean Elab Command in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← liftTermElabM <| Lean.collectAxioms ``imported_torsion_order do
    unless standard.contains axiomName do
      throwError "Unexpected rational torsion axiom {axiomName}"
