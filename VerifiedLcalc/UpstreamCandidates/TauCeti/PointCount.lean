/-
Copyright (c) 2026 Kevin H Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin H Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.Tactic.Linarith

/-! # Computable point counts for finite Weierstrass models -/

@[expose] public section

namespace WeierstrassCurve

section FiniteCommutativeRing
variable {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]

/-- An executable projective-model point count over an explicitly enumerated
finite field. Singular affine solutions and the point at infinity are included.
Unlike `pointCount`, this definition needs no classical choice. -/
def pointCountFinite (W : WeierstrassCurve F) : ℕ :=
  letI : DecidablePred (fun p : F × F => W.toAffine.Equation p.1 p.2) :=
    fun p => decidable_of_iff
      (p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 =
        p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆)
      (W.toAffine.equation_iff p.1 p.2).symm
  Fintype.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1

/-- Cardinality specification valid for all finite commutative rings. -/
theorem pointCountFinite_def (W : WeierstrassCurve F) :
    W.pointCountFinite = Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1 := by
  unfold pointCountFinite
  exact congrArg (fun n : ℕ => n + 1) (@Fintype.card_eq_nat_card _ _)

/-- Infinity contributes one point even for a singular equation. -/
theorem one_le_pointCountFinite (W : WeierstrassCurve F) : 1 ≤ W.pointCountFinite := by
  rw [pointCountFinite_def]
  omega

/-- Elementary bound on all affine solutions; no ellipticity is required. -/
theorem pointCountFinite_le (W : WeierstrassCurve F) :
    W.pointCountFinite ≤ Fintype.card F ^ 2 + 1 := by
  rw [pointCountFinite_def]
  have h := Nat.card_le_card_of_injective
    (Subtype.val : {p : F × F // W.toAffine.Equation p.1 p.2} → F × F)
    Subtype.val_injective
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod, pow_two] using
    Nat.add_le_add_right h 1

/-- Executable trace from the finite-field point-count algorithm. -/
def frobeniusTraceFinite (W : WeierstrassCurve F) : ℤ :=
  (Fintype.card F : ℤ) + 1 - W.pointCountFinite

/-- A deliberately weak trace bound requiring only finite-ring counting. -/
theorem frobeniusTraceFinite_abs_le_square (W : WeierstrassCurve F) :
    |W.frobeniusTraceFinite| ≤ (Fintype.card F : ℤ) ^ 2 := by
  have hlo : (1 : ℤ) ≤ W.pointCountFinite := by exact_mod_cast W.one_le_pointCountFinite
  have hhi : (W.pointCountFinite : ℤ) ≤ (Fintype.card F : ℤ) ^ 2 + 1 := by
    exact_mod_cast W.pointCountFinite_le
  have hq : (1 : ℤ) ≤ Fintype.card F := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : F)⟩)
  have hqq : (Fintype.card F : ℤ) ≤ (Fintype.card F : ℤ) ^ 2 :=
    le_self_pow₀ hq (by decide)
  unfold frobeniusTraceFinite
  apply abs_le.mpr
  constructor <;> nlinarith

end FiniteCommutativeRing

section FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Executable enumeration computes exactly TauCeti's existing count. -/
theorem pointCountFinite_eq_pointCount (W : WeierstrassCurve F) :
    W.pointCountFinite = W.pointCount := by
  rw [pointCountFinite_def, pointCount_def]

/-- Executable trace computes exactly TauCeti's existing Frobenius trace. -/
theorem frobeniusTraceFinite_eq_frobeniusTrace (W : WeierstrassCurve F) :
    W.frobeniusTraceFinite = W.frobeniusTrace := by
  simp only [frobeniusTraceFinite, frobeniusTrace_def, pointCountFinite_eq_pointCount,
    Nat.card_eq_fintype_card]

end FiniteField

/-- Transport the projective equation count through an actual residue-field
isomorphism; singular points remain included. -/
theorem pointCount_map_equiv {F K : Type*} [Field F] [Field K]
    (W : WeierstrassCurve F) (k : F ≃+* K) :
    (W.map k.toRingHom).pointCount = W.pointCount := by
  rw [WeierstrassCurve.pointCount_def, WeierstrassCurve.pointCount_def]
  congr 1
  apply Nat.card_congr
  exact ((k.toEquiv.prodCongr k.toEquiv).subtypeEquiv
    (fun xy => (W.toAffine.map_equation (f := k.toRingHom) k.injective xy.1 xy.2).symm)).symm

theorem frobeniusTrace_map_equiv {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    (W : WeierstrassCurve F) (k : F ≃+* K) :
    (W.map k.toRingHom).frobeniusTrace = W.frobeniusTrace := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.frobeniusTrace_def,
    pointCount_map_equiv, Nat.card_congr k.toEquiv]

end WeierstrassCurve
