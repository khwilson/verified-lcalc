/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Verification.DegreeTwoIsogeny
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Check an exact affine Vélu kernel with zero y-coordinate -/

public section

namespace VerifiedLcalc
open TauCeti WeierstrassCurve WeierstrassCurve.Affine

open scoped BigOperators
section PairKernel

variable {G : Type*} [Group G]
@[to_additive twoKernel]
private def twoKernelMul (P : G) (h : P * P = 1) : Subgroup G where
  carrier := {1, P}
  one_mem' := Set.mem_insert 1 _
  mul_mem' := by
    intro a b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl) (rfl | rfl) <;> simp [h]
  inv_mem' := by
    have hn : P⁻¹ = P := (eq_inv_of_mul_eq_one_left h).symm
    intro a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl) <;> simp [hn]

@[to_additive pointInKernel]
private def pointInKernelMul (P : G) (h : P * P = 1) : twoKernelMul P h :=
  ⟨P, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩

@[to_additive kernelEquiv]
private noncomputable def kernelEquivMul (P : G) (h : P * P = 1) (hne : P ≠ 1) :
    Bool ≃ twoKernelMul P h := by
  let f : Bool → twoKernelMul P h := fun b => if b then pointInKernelMul P h else 1
  have hf0 : f false = 1 := rfl
  have hf1 : f true = pointInKernelMul P h := rfl
  have hp : pointInKernelMul P h ≠ 1 := fun he => hne (congrArg Subtype.val he)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp_all
  · rintro ⟨a, ha⟩
    change a = 1 ∨ a = P at ha
    rcases ha with rfl | rfl
    · exact ⟨false, hf0⟩
    · exact ⟨true, hf1⟩

@[to_additive sum_kernel]
private theorem prod_kernelMul {M : Type*} [CommMonoid M] (P : G) (h : P * P = 1)
    (hne : P ≠ 1) [Fintype (twoKernelMul P h)] (f : twoKernelMul P h → M) :
    (∏ q : twoKernelMul P h, f q) = f 1 * f (pointInKernelMul P h) := by
  rw [← Fintype.prod_equiv (kernelEquivMul P h hne) (f ∘ kernelEquivMul P h hne) f
    (fun _ => rfl)]
  rw [Fintype.prod_bool]
  change f (pointInKernelMul P h) * f 1 = _
  exact mul_comm _ _

end PairKernel

private theorem velu_zero_y_identity {K : Type*} [Field K] (A B C r x y : K) (hne : x - r ≠ 0)
    (hr : r ^ 3 + A * r ^ 2 + B * r + C = 0)
    (hy : y ^ 2 = x ^ 3 + A * x ^ 2 + B * x + C) :
    let d := 3 * r ^ 2 + 2 * A * r + B
    let ell := y / (x - r)
    let tx := ell ^ 2 - A - x - r
    let X := x + tx - r
    let Y := ell * (x - tx)
    Y ^ 2 = X ^ 3 + A * X ^ 2 + (B - 5 * d) * X + (C - (4 * A + 7 * r) * d) := by
  let d := 3 * r ^ 2 + 2 * A * r + B
  have hc : C = -(r ^ 3 + A * r ^ 2 + B * r) := by linear_combination hr
  have hell : (y / (x - r)) ^ 2 = x + A + 2 * r + d / (x - r) := by
    rw [div_pow, hy, hc]
    dsimp [d]
    field_simp [hne]
    ring
  have hY : y / (x - r) * (x - ((y / (x - r)) ^ 2 - A - x - r)) =
      y * (1 - d / (x - r) ^ 2) := by
    rw [hell]
    field_simp [hne]
    ring
  dsimp only
  rw [hY, hell, mul_pow, hy, hc]
  dsimp [d]
  field_simp [hne]
  ring


/-- Compute the normalized quotient equation for a kernel point `(r,0)` when a₁=a₃=0. -/
@[expose] def zeroYVeluTarget (W : WeierstrassCurve ℚ) (r : ℚ) : WeierstrassCurve ℚ :=
  let d := 3 * r ^ 2 + 2 * W.a₂ * r + W.a₄
  ⟨0, W.a₂, 0, W.a₄ - 5 * d, W.a₆ - (4 * W.a₂ + 7 * r) * d⟩

private theorem zeroY_point_add_self (W : WeierstrassCurve ℚ) (r : ℚ)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0)
    (h : (W.baseChange ℚ).toAffine.Nonsingular r 0) :
    let P : (W.baseChange ℚ).toAffine.Point := .some r 0 h
    P + P = 0 := by
  dsimp only
  let P : (W.baseChange ℚ).toAffine.Point := .some r 0 h
  have hn : -P = P := by
    change -(.some r 0 h) = (.some r 0 h : (W.baseChange ℚ).toAffine.Point)
    rw [Point.neg_some, Point.some.injEq]
    simp [Affine.negY, WeierstrassCurve.baseChange, WeierstrassCurve.map, h₁, h₃]
  calc
    P + P = -P + P := congrArg (· + P) hn.symm
    _ = 0 := neg_add_cancel _

private theorem zeroY_nonsingular (W : WeierstrassCurve ℚ) [W.IsElliptic] (r : ℚ)
    (hr : r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆ = 0) :
    (W.baseChange ℚ).toAffine.Nonsingular r 0 := by
  apply Affine.equation_iff_nonsingular.mp
  simpa [Affine.equation_iff, WeierstrassCurve.baseChange, WeierstrassCurve.map, eq_comm]
    using hr

private theorem zeroY_translation (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (r : ℚ) (hn : (W.baseChange ℚ).toAffine.Nonsingular r 0)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    let P : (W.baseChange ℚ).toAffine.Point := .some r 0 hn
    let x := W.toAffine.genericX
    let y := W.toAffine.genericY
    let a := algebraMap ℚ W.toAffine.FunctionField
    let l := y / (x - a r)
    let tx := l ^ 2 - a W.a₂ - x - a r
    W.toAffine.translation P x = tx ∧ W.toAffine.translation P y = l * (x - tx) - y := by
  dsimp only
  have hx := W.toAffine.genericX_ne_algebraMap r
  constructor
  · rw [translation_apply_genericX_some, Affine.slope_of_X_ne hx]
    simp [Affine.addX, WeierstrassCurve.baseChange, WeierstrassCurve.map, h₁]
  · rw [translation_apply_genericY_some, Affine.slope_of_X_ne hx]
    simp [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, h₁, h₃]
    ring

private theorem zeroYVelu_eq (W : WeierstrassCurve ℚ) [W.IsElliptic] (r : ℚ)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0)
    (hr : r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆ = 0) (hn := zeroY_nonsingular W r hr) :
    let P : (W.baseChange ℚ).toAffine.Point := .some r 0 hn
    let h₂ := zeroY_point_add_self W r h₁ h₃ hn
    let Φ := twoKernel P h₂
    let _ : Finite Φ := Finite.of_equiv Bool (kernelEquiv P h₂ (Point.some_ne_zero hn))
    veluCurve W.toAffine Φ = zeroYVeluTarget W r := by
  dsimp only
  symm
  classical
  let P : (W.baseChange ℚ).toAffine.Point := .some r 0 hn
  let h₂ := zeroY_point_add_self W r h₁ h₃ hn
  let Φ := twoKernel P h₂
  let _ : Finite Φ := Finite.of_equiv Bool (kernelEquiv P h₂ (Point.some_ne_zero hn))
  apply eq_veluCurve_of_equation W.toAffine Φ
  let _ : Fintype Φ := Fintype.ofFinite Φ
  let x := W.toAffine.genericX
  let y := W.toAffine.genericY
  let a := algebraMap ℚ W.toAffine.FunctionField
  let l := y / (x - a r)
  let tx := l ^ 2 - a W.a₂ - x - a r
  have hx : x ≠ a r := W.toAffine.genericX_ne_algebraMap r
  have hy : y ^ 2 = x ^ 3 + a W.a₂ * x ^ 2 + a W.a₄ * x + a W.a₆ := by
    simpa [Affine.equation_iff, x, y, a, WeierstrassCurve.baseChange, WeierstrassCurve.map, h₁, h₃]
      using W.toAffine.equation_genericX_genericY
  obtain ⟨htrX, htrY⟩ := zeroY_translation W r hn h₁ h₃
  change W.toAffine.translation P x = tx at htrX
  change W.toAffine.translation P y = l * (x - tx) - y at htrY
  have hX : veluX W.toAffine Φ = x + tx - a r := by
    rw [veluX_def, sum_kernel P h₂ (Point.some_ne_zero hn),
      sum_kernel P h₂ (Point.some_ne_zero hn)]
    change W.toAffine.translation 0 x + W.toAffine.translation P x -
      a (Point.xCoord 0 + P.xCoord) = _
    rw [htrX]
    simp [P]
  have hY : veluY W.toAffine Φ = l * (x - tx) := by
    rw [veluY_def, sum_kernel P h₂ (Point.some_ne_zero hn),
      sum_kernel P h₂ (Point.some_ne_zero hn)]
    change W.toAffine.translation 0 y + W.toAffine.translation P y -
      a (Point.yCoord 0 + P.yCoord) = _
    rw [htrY]
    simp [P]
  change ((zeroYVeluTarget W r).baseChange W.toAffine.FunctionField).toAffine.Equation
    (veluX W.toAffine Φ) (veluY W.toAffine Φ)
  rw [hX, hY]
  have hr' : a r ^ 3 + a W.a₂ * (a r) ^ 2 + a W.a₄ * a r + a W.a₆ = 0 := by
    simpa only [map_add, map_mul, map_pow, map_zero] using congrArg a hr
  let d := 3 * r ^ 2 + 2 * W.a₂ * r + W.a₄
  let X := x + tx - a r
  let Y := l * (x - tx)
  rw [Affine.equation_iff]
  change Y ^ 2 + a 0 * X * Y + a 0 * Y =
    X ^ 3 + a W.a₂ * X ^ 2 + a (W.a₄ - 5 * d) * X + a (W.a₆ - (4 * W.a₂ + 7 * r) * d)
  simp only [d, map_zero, zero_mul, add_zero, map_add, map_sub, map_mul, map_pow, map_ofNat]
  exact velu_zero_y_identity (a W.a₂) (a W.a₄) (a W.a₆) (a r) x y (sub_ne_zero.mpr hx) hr' hy


/-- Verify raw exact equations and a specified affine degree-two kernel point. -/
noncomputable def DegreeTwoIsogenyFact.ofZeroY (source target : WeierstrassCurve ℤ)
    [(source.baseChange ℚ).IsElliptic] [(target.baseChange ℚ).IsElliptic]
    (r : ℚ) (h₁ : (source.baseChange ℚ).a₁ = 0) (h₃ : (source.baseChange ℚ).a₃ = 0)
    (hr : let W := source.baseChange ℚ; r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆ = 0)
    (hquot : zeroYVeluTarget (source.baseChange ℚ) r = target.baseChange ℚ)
    (hj : (source.baseChange ℚ).j ≠ (target.baseChange ℚ).j) :
    DegreeTwoIsogenyFact source target := by
  let W := source.baseChange ℚ
  let hn := zeroY_nonsingular W r hr
  let P : (W.baseChange ℚ).toAffine.Point := .some r 0 hn
  let h₂ := zeroY_point_add_self W r h₁ h₃ hn
  let Φ := twoKernel P h₂
  let enum := kernelEquiv P h₂ (Point.some_ne_zero hn)
  letI : Finite Φ := Finite.of_equiv Bool enum
  apply ofVelu source target Φ _ 1 _ hj
  · rw [← Nat.card_congr enum]
    simp
  · rw [one_smul]
    exact congrArg WeierstrassCurve.toAffine ((zeroYVelu_eq W r h₁ h₃ hr).trans hquot)

end VerifiedLcalc
