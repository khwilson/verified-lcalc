/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Integral-point membership (TauCeti excerpt)

Retains the coordinate construction, membership predicate and negation lemmas
from TauCeti's `Affine/Point/Integral.lean`. See `PROVENANCE.json` for the source
revision. Finite searches and change-of-variables results are omitted.
-/

public section

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℤ)

-- The affine curve of the rational base change is the coefficientwise map of the integral curve.
private theorem integral_toAffine_baseChange :
    (W.baseChange ℚ).toAffine = W.toAffine.map (Int.castRingHom ℚ) := by
  rfl

/-- The rational base change satisfies the Weierstrass equation at integer-cast coordinates
exactly when the integral model does. Not to be confused with
`WeierstrassCurve.Affine.equation_baseChange_iff`, which expands the coefficients of a base
change. -/
theorem equation_baseChange_iff_intCast {x y : ℤ} :
    (W.baseChange ℚ).toAffine.Equation (x : ℚ) (y : ℚ) ↔ W.toAffine.Equation x y := by
  rw [W.integral_toAffine_baseChange]
  simpa only [Int.coe_castRingHom] using
    Affine.map_equation W.toAffine (f := Int.castRingHom ℚ) Int.cast_injective x y

section

variable [(W.baseChange ℚ).IsElliptic]

/-- An integral solution of the affine Weierstrass equation determines a rational point. -/
def pointOfIntegralSolution (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.Point :=
  .mk (W.equation_baseChange_iff_intCast.mpr h)

-- Not a `simp` lemma: it would rewrite the left-hand sides of `pointOfIntegralSolution_mem` and
-- the `pointEquiv` lemmas, which are themselves in `simp` normal form.
/-- The point built from an integral solution is the affine point with those coordinates. -/
theorem pointOfIntegralSolution_eq_some (x y : ℤ) (h : W.toAffine.Equation x y) :
    W.pointOfIntegralSolution x y h =
      .some (x : ℚ) (y : ℚ)
        (Affine.equation_iff_nonsingular.mp (W.equation_baseChange_iff_intCast.mpr h)) := by
  simp only [pointOfIntegralSolution, Affine.Point.mk]

/-- The affine coordinates of the rational point constructed from an integral solution. -/
@[simp]
theorem pointEquiv_pointOfIntegralSolution (x y : ℤ) (h : W.toAffine.Equation x y) :
    (W.baseChange ℚ).toAffine.pointEquiv (W.pointOfIntegralSolution x y h) =
      .some ⟨⟨(x : ℚ), (y : ℚ)⟩, by
        exact W.equation_baseChange_iff_intCast.mpr h⟩ := by
  simp only [pointOfIntegralSolution, Affine.pointEquiv_some]
  congr 1

/-- The affine rational points with both coordinates integral. The point at infinity is excluded. -/
def integralPoints : Set (W.baseChange ℚ).toAffine.Point :=
  {P | ∃ x y : ℤ, ∃ h : W.toAffine.Equation x y, P = W.pointOfIntegralSolution x y h}

/-- A rational affine point is integral exactly when it comes from an integer solution of the
Weierstrass equation. -/
theorem mem_integralPoints_iff (P : (W.baseChange ℚ).toAffine.Point) :
    P ∈ W.integralPoints ↔
      ∃ x y : ℤ, ∃ h : W.toAffine.Equation x y, P = W.pointOfIntegralSolution x y h :=
  Iff.rfl

/-- Every integral solution gives an integral point. -/
@[simp]
theorem pointOfIntegralSolution_mem (x y : ℤ) (h : W.toAffine.Equation x y) :
    W.pointOfIntegralSolution x y h ∈ W.integralPoints :=
  ⟨x, y, h, rfl⟩

/-- The point at infinity, denoted by `0`, is not an affine integral point. -/
@[simp]
theorem zero_not_mem_integralPoints :
    (0 : (W.baseChange ℚ).toAffine.Point) ∉ W.integralPoints := by
  rintro ⟨x, y, h, heq⟩
  simp [pointOfIntegralSolution, Affine.Point.mk] at heq

/-- Integral points are stable under the group inverse because
`-(x,y) = (x,-y-a₁x-a₃)` has integral coordinates. -/
theorem neg_mem_integralPoints {P : (W.baseChange ℚ).toAffine.Point}
    (hP : P ∈ W.integralPoints) : -P ∈ W.integralPoints := by
  obtain ⟨x, y, h, rfl⟩ := hP
  let y' : ℤ := -y - W.a₁ * x - W.a₃
  have h' : W.toAffine.Equation x y' := by
    -- The chosen integer is exactly the Weierstrass negation formula.
    change W.toAffine.Equation x (W.toAffine.negY x y)
    exact (W.toAffine.equation_neg _ _).2 h
  refine ⟨x, y', h', ?_⟩
  simp only [pointOfIntegralSolution, Affine.Point.mk, Affine.Point.neg_some]
  congr 1
  rw [W.integral_toAffine_baseChange]
  exact W.toAffine.map_negY (Int.castRingHom ℚ) x y

/-- Negation preserves and reflects integrality of affine points. -/
@[simp]
theorem neg_mem_integralPoints_iff {P : (W.baseChange ℚ).toAffine.Point} :
    -P ∈ W.integralPoints ↔ P ∈ W.integralPoints := by
  constructor
  · intro hP
    have h := W.neg_mem_integralPoints hP
    simpa only [neg_neg] using h
  · exact W.neg_mem_integralPoints

end

end WeierstrassCurve
