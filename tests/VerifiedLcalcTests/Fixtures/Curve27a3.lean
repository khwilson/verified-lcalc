/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic

/-! # All rational points of the LMFDB curve `27.a3` -/

@[expose] public section

namespace VerifiedLcalc.Examples.Curve27a3

open WeierstrassCurve

/-- The integral model `y² + y = x³ - 7` of `27.a3`. -/
abbrev curve : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, -7⟩

instance : (curve.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- Fermat's theorem for cubes exhausts the rational solutions of this equation. -/
theorem rationalCoordinates {x y : ℚ} (h : y ^ 2 + y = x ^ 3 - 7) :
    x = 3 ∧ (y = -5 ∨ y = 4) := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at h
    nlinarith [sq_nonneg (2 * y + 1)]
  have hsum : (y + 5) ^ 3 + (4 - y) ^ 3 = (3 * x) ^ 3 := by
    linear_combination 27 * h
  have hy : y = -5 ∨ y = 4 := by
    by_contra! hy
    exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree)
      (y + 5) (4 - y) (3 * x) (by intro he; apply hy.1; linarith)
      (by intro he; apply hy.2; linarith) (mul_ne_zero (by norm_num) hx) hsum
  have hc : x ^ 3 = (3 : ℚ) ^ 3 := by
    rcases hy with rfl | rfl <;> norm_num at h ⊢ <;> linarith
  exact ⟨(Odd.strictMono_pow (show Odd 3 from ⟨1, rfl⟩)).injective hc, hy⟩

/-- Every affine integral point on this curve has abscissa `3`. -/
def integralSupport : IntegralXSupport curve where
  xs := [3]
  covers x y hy := by
    have he : y ^ 2 + y = x ^ 3 - 7 := by
      simpa [Affine.equation_iff, curve, toAffine, sub_eq_add_neg] using hy
    have hx := (rationalCoordinates (x := (x : ℚ)) (y := (y : ℚ)) (by exact_mod_cast he)).1
    exact List.mem_singleton.mpr (by exact_mod_cast hx)

/-- The rational curve has exactly its two affine points and the point at infinity. -/
theorem natCard_rational_points : Nat.card (curve.baseChange ℚ).toAffine.Point = 3 := by
  let first : (curve.baseChange ℚ).toAffine.Point :=
    curve.pointOfIntegralSolution 3 (-5) (by norm_num [Affine.equation_iff, curve, toAffine])
  let second : (curve.baseChange ℚ).toAffine.Point :=
    curve.pointOfIntegralSolution 3 4 (by norm_num [Affine.equation_iff, curve, toAffine])
  let points : Finset (curve.baseChange ℚ).toAffine.Point := {0, first, second}
  have covers (P : (curve.baseChange ℚ).toAffine.Point) : P ∈ points := by
    cases P with
    | zero => simp [points, Affine.Point.zero_def]
    | some x y h =>
      have he : y ^ 2 + y = x ^ 3 - 7 := by
        simpa [Affine.equation_iff, baseChange, curve, toAffine, sub_eq_add_neg] using h.1
      obtain ⟨rfl, rfl | rfl⟩ := rationalCoordinates he
      · simp [points, first, pointOfIntegralSolution_eq_some]
      · simp [points, second, pointOfIntegralSolution_eq_some]
  let : Fintype (curve.baseChange ℚ).toAffine.Point := ⟨points, covers⟩
  rw [Nat.card_eq_fintype_card]
  have h12 : first ≠ second := by
    norm_num [first, second, pointOfIntegralSolution_eq_some]
  have hz : (0 : (curve.baseChange ℚ).toAffine.Point) ∉
      ({first, second} : Finset (curve.baseChange ℚ).toAffine.Point) := by
    simp [first, second, Affine.Point.zero_def, pointOfIntegralSolution_eq_some]
  change (insert 0 ({first, second} : Finset (curve.baseChange ℚ).toAffine.Point)).card = 3
  rw [Finset.card_insert_of_notMem hz, Finset.card_pair_eq_two_iff.mpr h12]

/-- Finiteness of the rational point group proves Mordell–Weil rank zero. -/
theorem rank_eq_zero : Module.rank ℤ (curve.baseChange ℚ).toAffine.Point = 0 := by
  let : Finite (curve.baseChange ℚ).toAffine.Point :=
    Nat.finite_of_card_ne_zero (by rw [natCard_rational_points]; decide)
  exact Module.rank_eq_zero_iff_isTorsion.mpr
    (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite)

/-- Independently proved abscissa support and rank of the same equation. -/
def proofs : IntegralCurveProofs curve :=
  { integralXSupport := some integralSupport
    algebraicRank := some (.ofRankEq 0 (by simpa using rank_eq_zero)) }

certify_ec Checked from_json_string
  r#"{"ainvs":[0,0,1,0,-7],"xcoord_integral_points":[3,3],"num_int_pts":2,"rank":0}"#
  with_proofs proofs

end VerifiedLcalc.Examples.Curve27a3
