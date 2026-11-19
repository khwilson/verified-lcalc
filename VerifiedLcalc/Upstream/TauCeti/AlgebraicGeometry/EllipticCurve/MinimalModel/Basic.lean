/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An integral Weierstrass equation whose `c₄` is a unit at the place is minimal.** No change of
variables can increase the valuation of the discriminant: it scales `Δ` by `u⁻¹²` while scaling
`c₄` by `u⁻⁴`, and integrality of the transformed equation forces `v (u⁻⁴) ≤ 1`.

This is the unit-`c₄` case of the Kraus–Laska criterion (Silverman, *AEC*, Remark VII.1.1). The
hypothesis is phrased through the adic valuation of `W.c₄ : K` to match
`WeierstrassCurve.HasMultiplicativeReduction`, so that a curve for which only `c₄` has been
computed can be given its `IsMinimal` field. -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : valuation K (maximalIdeal R) (C • W).c₄ ≤ 1 := by
    simpa [← integralModel_c₄_eq R (C • W)] using valuation_le_one _ _
  rw [variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at hint
  simpa [variableChange_Δ, map_mul, map_pow] using mul_le_of_le_one_left'
    (pow_le_one' ((pow_le_one_iff (by norm_num)).mp hint) 12)

/-- **Mathlib's chosen minimal equation lies in the variable-change orbit.** The equation
`W.minimal R` is obtained from `W` by a change of variables. -/
theorem exists_smul_eq_minimal (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, C • W = W.minimal R :=
  ⟨_, rfl⟩

/-- The chosen minimal equations of two equations related by a change of variables are themselves
related by a change of variables. -/
theorem exists_smul_minimal_eq_minimal (D : VariableChange K) (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, C • W.minimal R = (D • W).minimal R := by
  obtain ⟨C₁, hC₁⟩ := W.exists_smul_eq_minimal R
  obtain ⟨C₂, hC₂⟩ := (D • W).exists_smul_eq_minimal R
  refine ⟨C₂ * D * C₁⁻¹, ?_⟩
  rw [mul_smul, mul_smul, ← hC₁, inv_smul_smul, hC₂]

/-! ### Comparing two minimal models

`IsMinimal` says the discriminant valuation is maximal among integral models. Two minimal models of
the same curve therefore pin each other: each is at least as good as the other, so their
valuations agree, and the change of variables between them can only scale `Δ` by a unit. -/

/-- **A minimal model maximises the discriminant valuation in its orbit**: every integral model
obtained from it by a change of variables has discriminant of at most that valuation. This is the
`valuation`-level reading of Mathlib's `IsMinimal`, whose `MaximalFor` phrasing speaks of
`valuation_Δ_aux` and of the orbit of a fixed equation. -/
theorem valuation_Δ_le_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [hm : IsMinimal R W₁]
    [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ ≤ valuation K (maximalIdeal R) W₁.Δ := by
  have hint : IsIntegral R (D • W₁) := by rw [hD]; infer_instance
  have h : valuation_Δ_aux R (D • W₁) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W₁) :=
    (le_total (valuation_Δ_aux R ((1 : VariableChange K) • W₁)) (valuation_Δ_aux R (D • W₁))).elim
      (hm.val_Δ_maximal.2 hint) id
  rw [hD, one_smul] at h
  rw [← valuation_Δ_aux_eq_of_isIntegral R W₂, ← valuation_Δ_aux_eq_of_isIntegral R W₁,
    Subtype.coe_le_coe]
  exact h

/-- **Two minimal models related by a change of variables have the same discriminant valuation.**
So `v (Δ)` is an invariant of the curve at this place rather than of the chosen model: any two
minimal models of the same curve agree on it, and a consumer may read it off whichever model it
holds. -/
theorem valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ :=
  -- Antisymmetry: `D` carries `W₁` to `W₂` and `D⁻¹` carries `W₂` back, and by minimality neither
  -- direction can increase the valuation.
  le_antisymm (valuation_Δ_le_of_isMinimal_smul R D hD)
    (valuation_Δ_le_of_isMinimal_smul R D⁻¹ (by rw [← hD, inv_smul_smul]))

/-- **An integral model whose discriminant valuation matches that of a minimal model in its orbit
is itself minimal.** Together with `valuation_Δ_le_of_isMinimal_smul` this makes the discriminant
valuation a complete test for minimality among integral models of one curve. -/
theorem isMinimal_of_valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂)
    (h : valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ) :
    IsMinimal R W₂ := by
  refine ⟨⟨by simpa using ‹IsIntegral R W₂›, fun {C} hC _ => ?_⟩⟩
  dsimp only at hC ⊢
  have hint : IsIntegral R (C • W₂) := hC
  have hCD : (C * D) • W₁ = C • W₂ := by rw [mul_smul, hD]
  rw [← Subtype.coe_le_coe, one_smul, valuation_Δ_aux_eq_of_isIntegral R (C • W₂),
    valuation_Δ_aux_eq_of_isIntegral R W₂, h]
  exact valuation_Δ_le_of_isMinimal_smul R (C * D) hCD

/-- **A change of variables defined over `R` preserves minimality**: if `W` is minimal over `R`
and `C` is a change of variables with coefficients in `R`, then `C • W` is minimal over `R`. With
`valuation_u_eq_one_of_isMinimal_smul` and
`VariableChange.exists_baseChange_eq_of_smul_eq` in the other direction, the changes of variables
between minimal models of an elliptic curve are exactly those defined over `R`. -/
theorem isMinimal_baseChange_smul (W : WeierstrassCurve K) [IsMinimal R W]
    (C : VariableChange R) : IsMinimal R (C.baseChange K • W) := by
  have hW : (C • W.integralModel R).baseChange K = C.baseChange K • W := by
    rw [baseChange, ← map_variableChange, ← baseChange, baseChange_integralModel_eq R W]
    rfl
  have : IsIntegral R (C.baseChange K • W) := ⟨⟨C • W.integralModel R, hW.symm⟩⟩
  refine isMinimal_of_valuation_Δ_eq_of_isMinimal_smul R (C.baseChange K) rfl ?_
  have hu : valuation K (maximalIdeal R) (algebraMap R K ↑C.u) = 1 := by
    rw [valuation_of_algebraMap, intValuation_eq_one_iff_mem_primeCompl]
    exact (IsLocalRing.notMem_maximalIdeal).2 (Units.isUnit _)
  rw [variableChange_Δ, map_mul, map_pow]
  simp [VariableChange.baseChange, hu]

/-- **The scaling factor of a change of variables between two minimal models of an elliptic curve
has valuation `1`.** Over a discrete valuation ring that says `u` is a **unit**: it and its inverse
are both integral, so such a change of variables is as integral as its coordinates allow. This is
the hypothesis `VariableChange.exists_baseChange_eq_of_smul_eq` asks for, and hence the step by
which a property of the reduction transfers between two minimal models of one curve. -/
theorem valuation_u_eq_one_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) ↑D.u = 1 := by
  -- A change of variables scales `Δ` by `u⁻¹²`. The two discriminant valuations agree and are
  -- nonzero, so `v (u)¹² = 1`, and the value group is torsion-free.
  have hΔ0 : valuation K (maximalIdeal R) W₁.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr W₁.isUnit_Δ.ne_zero
  have h12 : valuation K (maximalIdeal R) ↑D.u ^ 12 = 1 := by
    have key : valuation K (maximalIdeal R) W₁.Δ
        = (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 * valuation K (maximalIdeal R) W₁.Δ := by
      conv_lhs => rw [← valuation_Δ_eq_of_isMinimal_smul R D hD, ← hD, variableChange_Δ]
      rw [map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 = 1 :=
      mul_right_cancel₀ hΔ0 (key.symm.trans (one_mul _).symm)
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h12

namespace VariableChange

/-- The scaling factor between two minimal elliptic equations is the image of a unit of the
discrete valuation ring. -/
theorem exists_unit_algebraMap_eq_u_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K)
    (hD : D • W₁ = W₂) : ∃ u₀ : Rˣ, algebraMap R K u₀ = D.u := by
  obtain ⟨u₀, hau⟩ := associated_of_valuation_eq (A := R) 1 (↑D.u : K)
    (by rw [map_one]; exact (valuation_u_eq_one_of_isMinimal_smul R D hD).symm)
  rw [Units.smul_def, Algebra.smul_def, mul_one] at hau
  exact ⟨u₀, hau⟩

end VariableChange

end WeierstrassCurve
