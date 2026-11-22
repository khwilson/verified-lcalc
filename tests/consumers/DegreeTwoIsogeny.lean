import VerifiedLcalcTests.Fixtures.DegreeTwoIsogeny
import Lean

/-! # Compiled reuse and axiom audit of the minimum rational isogeny degree -/

open Lean Elab Command TauCeti VerifiedLcalc VerifiedLcalcTests.Isogeny112

example : edge.isogeny.degree = 2 :=
  edge.degree_eq

example (φ : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine) :
    2 ≤ φ.degree :=
  edge.degree_le φ

example : IsLeast (Set.range fun φ :
    Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine => φ.degree) 2 :=
  edge.isLeast_degree

example : letI := edge.source_elliptic
    IsAddCyclic edge.isogeny.ker :=
  edge.kernel_cyclic

example : ¬ Nonempty (DegreeTwoIsogenyFact source source) := by
  rintro ⟨wrong⟩
  have h := wrong.degree_le (Isogeny.id (source.baseChange ℚ).toAffine)
  simp at h

run_cmd do
  let declarations := [``edge, ``DegreeTwoIsogenyFact.ofVelu, ``DegreeTwoIsogenyFact.isLeast_degree]
  for name in declarations do
    for assumption in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
        throwError "Unexpected rational isogeny axiom: {assumption}"
