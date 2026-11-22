/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certification.DegreeTwoIsogeny
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The degree-two isogeny from LMFDB 112.a2 to 112.a1 -/

public section

namespace VerifiedLcalcTests.Isogeny112
open VerifiedLcalc TauCeti WeierstrassCurve WeierstrassCurve.Affine

open scoped BigOperators
section PairKernel

variable {G : Type*} [AddCommGroup G]
private def twoKernel (P : G) (h : P + P = 0) : AddSubgroup G where
  carrier := {0, P}
  zero_mem' := Set.mem_insert 0 _
  add_mem' := by
    intro a b
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl) (rfl | rfl) <;> simp [h]
  neg_mem' := by
    have hn : -P = P := (eq_neg_of_add_eq_zero_left h).symm
    intro a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl) <;> simp [hn]
private def pointInKernel (P : G) (h : P + P = 0) : twoKernel P h :=
  ⟨P, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩

private noncomputable def kernelEquiv (P : G) (h : P + P = 0) (hne : P ≠ 0) :
    Bool ≃ twoKernel P h := by
  let f : Bool → twoKernel P h := fun b => if b then pointInKernel P h else 0
  have hf0 : f false = 0 := rfl
  have hf1 : f true = pointInKernel P h := rfl
  have hp : pointInKernel P h ≠ 0 := fun he => hne (congrArg Subtype.val he)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    cases a <;> cases b <;> simp_all
  · rintro ⟨a, ha⟩
    change a = 0 ∨ a = P at ha
    rcases ha with rfl | rfl
    · exact ⟨false, hf0⟩
    · exact ⟨true, hf1⟩

private theorem sum_kernel {M : Type*} [AddCommMonoid M] (P : G) (h : P + P = 0) (hne : P ≠ 0)
    [Fintype (twoKernel P h)] (f : twoKernel P h → M) :
    (∑ q : twoKernel P h, f q) = f 0 + f (pointInKernel P h) := by
  rw [← Fintype.sum_equiv (kernelEquiv P h hne) (f ∘ kernelEquiv P h hne) f (fun _ => rfl)]
  rw [Fintype.sum_bool]
  change f (pointInKernel P h) + f 0 = _
  exact add_comm _ _

end PairKernel

private theorem velu112_identity {K : Type*} [Field K] (x y : K) (hne : x + 2 ≠ 0)
    (hy : y ^ 2 = x ^ 3 + x ^ 2 + 4) :
    let ell := y / (x + 2)
    let tx := ell ^ 2 + 1 - x
    let X := x + tx + 2
    let Y := ell * (x - tx)
    Y ^ 2 = X ^ 3 + X ^ 2 - 40 * X + 84 := by
  have hell : (y / (x + 2)) ^ 2 = x - 3 + 8 / (x + 2) := by
    field_simp [hne]
    linear_combination hy
  have hY : y / (x + 2) * (x - ((y / (x + 2)) ^ 2 + 1 - x)) =
      y * (1 - 8 / (x + 2) ^ 2) := by
    rw [hell]
    field_simp [hne]
    ring
  dsimp only
  rw [hY, hell, mul_pow, hy]
  field_simp [hne]
  ring

/-- The source equation `112.a2`. -/
def source : WeierstrassCurve ℤ := ⟨0, 1, 0, 0, 4⟩

/-- The target equation `112.a1`. -/
def target : WeierstrassCurve ℤ := ⟨0, 1, 0, -40, 84⟩

private abbrev srcAffine : Affine ℚ := (source.baseChange ℚ).toAffine
private abbrev tgtAffine : Affine ℚ := (target.baseChange ℚ).toAffine

instance : (source.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩
instance : (target.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

private theorem kernelPointNonsingular : (srcAffine.baseChange ℚ).toAffine.Nonsingular (-2) 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  norm_num [source, srcAffine, WeierstrassCurve.baseChange, WeierstrassCurve.map]

private def kernelPoint : (srcAffine.baseChange ℚ).toAffine.Point :=
  .some (-2) 0 kernelPointNonsingular

private theorem kernelPoint_ne_zero : kernelPoint ≠ 0 :=
  Point.some_ne_zero kernelPointNonsingular

private theorem kernelPoint_add_self : kernelPoint + kernelPoint = 0 := by
  have h : -kernelPoint = kernelPoint := by
    rw [kernelPoint, Point.neg_some, Point.some.injEq]
    decide +kernel
  calc
    kernelPoint + kernelPoint = -kernelPoint + kernelPoint := congrArg (· + kernelPoint) h.symm
    _ = 0 := neg_add_cancel _

private abbrev kernel := twoKernel kernelPoint kernelPoint_add_self

private instance : Finite kernel :=
  Finite.of_equiv Bool (kernelEquiv kernelPoint kernelPoint_add_self kernelPoint_ne_zero)

private theorem card_kernel : Nat.card kernel = 2 := by
  rw [← Nat.card_congr (kernelEquiv kernelPoint kernelPoint_add_self kernelPoint_ne_zero)]
  simp

private theorem veluQuotient_eq_target : veluCurve srcAffine kernel = tgtAffine := by
  symm
  apply eq_veluCurve_of_equation srcAffine kernel
  classical
  let _ : Fintype kernel := Fintype.ofFinite kernel
  let x := srcAffine.genericX
  let y := srcAffine.genericY
  have hxm : x ≠ algebraMap ℚ srcAffine.FunctionField (-2) :=
    srcAffine.genericX_ne_algebraMap (-2 : ℚ)
  have hn : x + 2 ≠ 0 := by
    have hne : x ≠ (-2 : srcAffine.FunctionField) := by
      simpa only [map_neg, map_ofNat] using hxm
    intro h
    apply hne
    linear_combination h
  have hy : y ^ 2 = x ^ 3 + x ^ 2 + 4 := by
    simpa [Affine.equation_iff, source, x, y, WeierstrassCurve.baseChange,
      WeierstrassCurve.map] using srcAffine.equation_genericX_genericY
  let l := y / (x + 2)
  let tx := l ^ 2 + 1 - x
  have xTranslate : srcAffine.translation kernelPoint x = tx := by
    rw [kernelPoint, translation_apply_genericX_some, Affine.slope_of_X_ne hxm]
    norm_num [source, tx, l, x, y, Affine.addX, WeierstrassCurve.baseChange,
      WeierstrassCurve.map]
    ring
  have yTranslate : srcAffine.translation kernelPoint y = l * (x - tx) - y := by
    rw [kernelPoint, translation_apply_genericY_some, Affine.slope_of_X_ne hxm]
    norm_num [source, tx, l, x, y, Affine.addY, Affine.negY, Affine.negAddY,
      Affine.addX, WeierstrassCurve.baseChange, WeierstrassCurve.map]
    ring
  have hX : veluX srcAffine kernel = x + tx + 2 := by
    rw [veluX_def, sum_kernel kernelPoint kernelPoint_add_self kernelPoint_ne_zero,
      sum_kernel kernelPoint kernelPoint_add_self kernelPoint_ne_zero]
    change srcAffine.translation 0 x + srcAffine.translation kernelPoint x -
      algebraMap ℚ srcAffine.FunctionField (Point.xCoord 0 + kernelPoint.xCoord) = _
    rw [xTranslate]
    simp [kernelPoint, sub_neg_eq_add]
  have hY : veluY srcAffine kernel = l * (x - tx) := by
    rw [veluY_def, sum_kernel kernelPoint kernelPoint_add_self kernelPoint_ne_zero,
      sum_kernel kernelPoint kernelPoint_add_self kernelPoint_ne_zero]
    change srcAffine.translation 0 y + srcAffine.translation kernelPoint y -
      algebraMap ℚ srcAffine.FunctionField (Point.yCoord 0 + kernelPoint.yCoord) = _
    rw [yTranslate]
    simp [kernelPoint]
  rw [hX, hY]
  simpa [Affine.equation_iff, target, tgtAffine, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, l, tx, sub_eq_add_neg] using
    velu112_identity x y hn hy

/-- The proved rational matrix edge has the attained minimum degree two. -/
noncomputable def edge : DegreeTwoIsogenyFact source target :=
  DegreeTwoIsogenyFact.ofVelu source target kernel card_kernel 1
    (by rw [one_smul, veluQuotient_eq_target]) (by
      simp only [WeierstrassCurve.j_eq]
      decide +kernel)

end VerifiedLcalcTests.Isogeny112
