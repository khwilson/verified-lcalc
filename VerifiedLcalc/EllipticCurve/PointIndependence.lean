module

public import VerifiedLcalc.EllipticCurve.AlgebraicRank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Independence from a certified separating matrix

A verified ℤ-linear map from the point group to a characteristic-zero field's
coordinate space turns independence into a finite determinant check. For
example, pairing against fixed points with a proved Néron–Tate pairing gives
such a map. The map's linearity and its values must be proved; supplying an
unrelated matrix of approximate heights is insufficient.

The linear algebra is Mathlib's determinant criterion, restriction of scalars,
and reflection of independence along a linear map. No additional height or
finite-generation assumptions enter this implication.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- A nonzero determinant of actual images proves integer independence. -/
theorem independent_of_separating_matrix {G K : Type*} [AddCommGroup G]
    [Field K] [CharZero K] {n : Nat} (points : Fin n → G)
    (separate : G →ₗ[ℤ] (Fin n → K))
    (hdet : (Matrix.of fun i j => separate (points j) i).det ≠ 0) :
    LinearIndependent ℤ points := by
  apply LinearIndependent.of_comp separate
  exact (Matrix.linearIndependent_cols_of_det_ne_zero hdet).restrict_scalars' ℤ

/-- The same exact matrix certificate gives a lower bound on algebraic rank. -/
theorem algebraic_rank_lower_bound_of_separating_matrix
    {W : WeierstrassCurve ℚ} {K : Type*} [Field K] [CharZero K] {n : Nat}
    (points : Fin n → W.toAffine.Point)
    (separate : W.toAffine.Point →ₗ[ℤ] (Fin n → K))
    (hdet : (Matrix.of fun i j => separate (points j) i).det ≠ 0) :
    (n : Cardinal) ≤ Module.rank ℤ W.toAffine.Point :=
  algebraic_rank_lower_bound points (independent_of_separating_matrix points separate hdet)

end VerifiedLcalc.EllipticCurve
