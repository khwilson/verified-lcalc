/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion

/-! # An independent rational generator coordinate on 189.b1 -/

@[expose] public section

namespace VerifiedLcalcTests.RationalIndependence

open VerifiedLcalc VerifiedLcalc.EllipticCurve WeierstrassCurve

/-- The integral equation for LMFDB 189.b1. -/
abbrev model : WeierstrassCurve ℤ := ⟨0, 0, 1, -3834, -91375⟩

/-- The rational abscissa of the supplied point. -/
abbrev generatorX : ℚ := -143 / 4

/-- The rational ordinate of the supplied point. -/
abbrev generatorY : ℚ := -3 / 8

private theorem nonsingular :
    (model.baseChange ℚ).toAffine.Nonsingular generatorX generatorY := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  norm_num [model, generatorX, generatorY, baseChange]

private theorem infiniteOrder :
    ¬ IsOfFinAddOrder (Affine.Point.some generatorX generatorY nonsingular) := by
  intro ht
  rcases isInteger_or_order_two_of_torsion_rat nonsingular ht with ⟨⟨k, hk⟩, _⟩ | ⟨ho, _⟩
  · have hn : generatorX.den ≠ 1 := by decide +kernel
    exact hn (by rw [← hk]; simp)
  · have hd := addOrderOf_nsmul_eq_zero (Affine.Point.some generatorX generatorY nonsingular)
    rw [ho, two_nsmul] at hd
    have hn : 2 * generatorY + (model.a₁ : ℚ) * generatorX + model.a₃ ≠ 0 := by
      decide +kernel
    exact hn (by simpa [Affine.evalEval_polynomialY, baseChange] using
      (Affine.Point.some_add_self_eq_zero_iff nonsingular).mp hd)

certify_ec Rank189 from_json_string
  r#"{"ainvs":[0,0,1,-3834,-91375],"gens":[[-143,-3,2]],"ngens":1,
      "independent_generator_points":[0]}"#
  with_independence (by
    apply LinearIndependent.of_subsingleton' (0 : Fin 1)
    intro a h
    by_contra hn
    exact infiniteOrder (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, hn, h⟩))

certify_ec Rank189Lean from
  { equation := model, integralCoordinates := some [],
    generatorCoordinates := some [(generatorX, generatorY)],
    independentGeneratorPoints := some [0] }
  with_independence Rank189.algebraic.points_independent

end VerifiedLcalcTests.RationalIndependence
