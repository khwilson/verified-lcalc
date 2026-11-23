/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
import Mathlib.Data.Finset.Max
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-! # Compute the finite summaries of a proved rational isogeny class -/

@[expose] public section

namespace VerifiedLcalc.IsogenyClassModel

variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
  (model : IsogenyClassModel curve)

/-- The set of matrix entries in the input curve's row. -/
def rowDegrees : Finset ℕ := Finset.univ.image (model.isogenyMatrix model.curveIndex)

/-- The set of entries occurring anywhere in the minimum-degree matrix. -/
def matrixEntries : Finset ℕ := Finset.univ.image fun ij : Fin model.classSize ×
    Fin model.classSize => model.isogenyMatrix ij.1 ij.2

/-- Matrix-entry membership means an indexed pair attains that value. -/
theorem mem_matrixEntries (n : ℕ) :
    n ∈ model.matrixEntries ↔ ∃ i j, model.isogenyMatrix i j = n := by
  simp [matrixEntries, Prod.exists]

/-- The input curve supplies an index, so the matrix is nonempty. -/
theorem matrixEntries_nonempty : model.matrixEntries.Nonempty :=
  ⟨_, (model.mem_matrixEntries _).2 ⟨model.curveIndex, model.curveIndex, rfl⟩⟩

/-- The maximum over the minimum degrees of all ordered pairs. -/
def maximumDegree : ℕ := model.matrixEntries.max' model.matrixEntries_nonempty

/-- The class summary uses only computation on the matrix and the supplied isogeny proofs. -/
noncomputable def toFacts : IsogenyClassFacts curve where
  toIsogenyClassData := model.toIsogenyClassData
  isogenies i j := Classical.choose (model.attained i j)
  degree_eq i j := Classical.choose_spec (model.attained i j)
  classDegree := model.maximumDegree
  classDegree_mem := (model.mem_matrixEntries _).1 (Finset.max'_mem _ _)
  le_classDegree i j := model.matrixEntries.le_max' _ ((model.mem_matrixEntries _).2 ⟨i, j, rfl⟩)
  isogenyDegrees := model.rowDegrees
  isogenyDegrees_eq := rfl

end VerifiedLcalc.IsogenyClassModel

namespace VerifiedLcalc.IsogenyClassFacts

open TauCeti

variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
  (facts : IsogenyClassFacts curve)

/-- The matrix written as rows of increasing finite indices. -/
def matrixRows : List (List ℕ) :=
  List.ofFn fun i => List.ofFn (facts.isogenyMatrix i)

/-- The selected row gives minimum degrees from the actual input curve to the representatives.
A variable change and its inverse transport the maps while preserving degree. -/
theorem isLeast_inputDegree (j : Fin facts.classSize) :
    IsLeast (Set.range fun φ : Isogeny (curve.baseChange ℚ).toAffine
      (facts.representatives j).toAffine => φ.degree) (facts.isogenyMatrix facts.curveIndex j) := by
  let C := facts.curveChange
  have hC : C • (curve.baseChange ℚ).toAffine =
      (facts.representatives facts.curveIndex).toAffine := facts.curveChange_eq
  have hInv : C⁻¹ • (facts.representatives facts.curveIndex).toAffine =
      (curve.baseChange ℚ).toAffine := by rw [← hC, inv_smul_smul]
  refine ⟨⟨(facts.isogenies facts.curveIndex j).comp (Isogeny.variableChangeIsogeny C hC), ?_⟩, ?_⟩
  · simp [Isogeny.degree_comp, facts.degree_eq]
  rintro d ⟨φ, rfl⟩
  have h := facts.degree_min facts.curveIndex j
    (φ.comp (Isogeny.variableChangeIsogeny C⁻¹ hInv))
  simpa [Isogeny.degree_comp] using h

end VerifiedLcalc.IsogenyClassFacts
