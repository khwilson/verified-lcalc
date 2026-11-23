/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import Mathlib.Algebra.Polynomial.OfFn
import TauCeti.Algebra.Polynomial.XPow.SubC
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion

/-! # Strict torsion growth for 64.a4 over ℚ(i)

The [LMFDB row](https://www.lmfdb.org/EllipticCurve/Q/data/64.a4) lists this
quadratic field. The new point is `(i, 0)`, and a rational preimage would
supply a rational square root of `-1`.
-/

@[expose] public section

namespace ExtensionDataFixture

open Polynomial WeierstrassCurve VerifiedLcalc

/-- The polynomial in the submitted quadratic row. -/
abbrev f : ℚ[X] := (TorsionGrowthFieldClaim.mk [1, 0, 1] 2).polynomial
private theorem f_eq : f = X ^ 2 + 1 := by
  ext n
  by_cases h : n < 3
  · interval_cases n <;> simp [f, TorsionGrowthFieldClaim.polynomial, coeff_X_pow, coeff_one]
  · have hn : 3 ≤ n := by omega
    have h₂ : n ≠ 2 := by omega
    have h₀ : n ≠ 0 := by omega
    simp [f, TorsionGrowthFieldClaim.polynomial, ofFn_coeff_eq_zero_of_ge _ hn,
      coeff_X_pow, coeff_one, h₂, h₀]
/-- The quadratic field in the submitted row. -/
abbrev K := AdjoinRoot f
/-- The submitted polynomial is irreducible over ℚ. -/
theorem f_irreducible : Irreducible f := f_eq ▸ Polynomial.irreducible_X_sq_add_one ℚ
local instance : Fact (Irreducible f) := ⟨f_irreducible⟩
/-- The integral Weierstrass model with Cremona label 64a4. -/
abbrev growthModel : WeierstrassCurve ℤ := ⟨0, 0, 0, 1, 0⟩
/-- The image of the polynomial variable. -/
noncomputable abbrev i : K := AdjoinRoot.root f
private theorem i_squared : i ^ 2 + 1 = 0 := by
  have e := congrArg (fun p => Polynomial.eval₂ (AdjoinRoot.of f) i p) f_eq
  rw [AdjoinRoot.eval₂_root] at e
  simpa using e.symm

noncomputable local instance : DecidableEq K := Classical.decEq _
private theorem onCurve : (growthModel.baseChange K).toAffine.Nonsingular i 0 := by
  have hΔ : growthModel.Δ = -64 := by decide +kernel
  apply (Affine.equation_iff_nonsingular_of_Δ_ne_zero (by
    norm_num [baseChange, map_Δ, hΔ]) ).mp
  rw [Affine.equation_iff]
  simp [baseChange, growthModel]
  linear_combination -i * i_squared
private noncomputable def extraPoint : (growthModel.baseChange K).toAffine.Point :=
  .some i 0 onCurve
private theorem extraPoint_double : extraPoint + extraPoint = 0 := by
  apply (Affine.Point.some_add_self_eq_zero_iff onCurve).mpr
  simp [Affine.evalEval_polynomialY, baseChange, growthModel]

private theorem extraPoint_new : ∀ P : (growthModel.baseChange ℚ).toAffine.Point,
    Affine.Point.map (Algebra.ofId ℚ K) P ≠ extraPoint := by
  rintro (_ | ⟨x, y, h⟩) heq
  · contradiction
  · rw [Affine.Point.map_some] at heq
    have hx := (Affine.Point.some.inj heq).1
    change algebraMap ℚ K x = i at hx
    have hn := i_squared
    rw [← hx] at hn
    have hr : x ^ 2 + 1 = 0 := (algebraMap ℚ K).injective (by simpa using hn)
    nlinarith [sq_nonneg x]

/-- A point of order two outside the image of rational base change. -/
def growthEvidence : TorsionGrowthFieldFact growthModel where
  polynomial := f
  irreducible := f_irreducible
  growth := by
    refine ⟨extraPoint, isOfFinAddOrder_iff_nsmul_eq_zero.mpr ?_, extraPoint_new⟩
    exact ⟨2, by decide, by simpa only [two_nsmul] using extraPoint_double⟩

local instance : (growthModel.baseChange ℚ).IsElliptic :=
  ⟨by norm_num [growthModel, baseChange, map_Δ, Δ, b₂, b₄, b₆, b₈]⟩

certify_ec Growth64 from_json_string
  r#"{"ainvs":[0,0,0,1,0],"degree":4,"torsion":2,
    "torsion_growth":{"degree":2,"field":[1,0,1],"torsion":[2,2],"lmfdb_label":"64.a4"}}"#
  with_proofs ({ torsionGrowthField := some growthEvidence } : IntegralCurveProofs growthModel)

end ExtensionDataFixture
