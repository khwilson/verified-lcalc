/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.RealizationData
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
public import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Fuchsian
public import TauCeti.NumberTheory.ModularForms.EichlerIntegral.Basic
public import TauCeti.NumberTheory.ModularForms.QExpansion.FunctionField
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-! # Pointed modular parametrizations, normalized differentials and period images -/

public noncomputable section
namespace VerifiedLcalc.Modularity

open Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint Subgroup
open CongruenceSubgroup TauCeti TauCeti.RiemannSurface UpperHalfPlane
open scoped MatrixGroups

/-- The effective action of the congruence subgroup defining the analytic curve of level `N`. -/
abbrev gammaZeroEffective (N : ℕ) : Subgroup PSL(2, ℝ) :=
  (Gamma0 N).map sl2zToPSL2R

/-- The cusp at infinity of the effective `Γ₀(N)` has identity scaling and width one.
The stabilizer argument is adapted from TauCeti's `cuspDatumInftyGamma`. -/
def cuspDatumInftyGammaZero (N : ℕ) : (gammaZeroEffective N).CuspDatum := by
  let γ : gammaZeroEffective N := ⟨sl2zToPSL2R ModularGroup.T,
    Subgroup.mem_map_of_mem _ (Gamma0_mem.mpr (by simp [ModularGroup.T]))⟩
  have hpow (m : ℤ) : ((γ ^ m : gammaZeroEffective N) : PSL(2, ℝ)) =
      sl2zToPSL2R (ModularGroup.T ^ m) := by
    rw [Subgroup.coe_zpow, map_zpow]
  have hγ : (γ : PSL(2, ℝ)) = upperRightHom 1 := by
    simpa using (hpow 1).trans (TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow 1)
  refine ⟨∞, 1, γ, 1, one_pos, le_antisymm ?_ ?_, by simpa using hγ⟩
  · rw [zpowers_le, mem_stabilizer_iff, Subgroup.smul_def, hγ]
    exact upperRightHom_smul_infty _
  · rintro ⟨_, a, ha, rfl⟩ hg
    have hc : a 1 0 = 0 :=
      (sl2zToPSL2R_smul_infty_eq_infty_iff a).mp (mem_stabilizer_iff.mp hg)
    refine mem_zpowers_iff.mpr ?_
    rcases ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with ha' | ha'
    · exact ⟨a 0 1, Subtype.ext ((hpow _).trans (congrArg sl2zToPSL2R ha'.symm))⟩
    · refine ⟨-(a 0 1), Subtype.ext ((hpow _).trans ?_)⟩
      exact ((congrArg sl2zToPSL2R ha').trans (sl2zToPSL2R_neg _)).symm

/-- The chosen cusp is infinity. -/
@[simp]
theorem cuspDatumInftyGammaZero_cusp (N : ℕ) :
    (cuspDatumInftyGammaZero N).cusp = ∞ := (rfl)

/-- The chosen scaling is the identity. -/
@[simp]
theorem cuspDatumInftyGammaZero_scaling (N : ℕ) :
    (cuspDatumInftyGammaZero N).scaling = 1 := (rfl)

/-- The chosen cusp has width one. -/
@[simp]
theorem cuspDatumInftyGammaZero_width (N : ℕ) :
    (cuspDatumInftyGammaZero N).width = 1 := (rfl)

/-- The rational function field on compactified `Γ₀(N)`, using the rational
Fourier coefficients at the normalized cusp at infinity. -/
@[expose] def gammaZeroFunctionField (N : ℕ) [NeZero N] :
    Subfield (MeromorphicFunction (gammaZeroEffective N).CompactifiedQuotient) :=
  CompactifiedQuotient.coeffSubfield (cuspDatumInftyGammaZero N) ⊥

/-- A nonconstant rational map from compactified `Γ₀(N)` to the given elliptic curve,
represented contravariantly by its injection on rational function fields. -/
abbrev ModularPullback (N : ℕ) [NeZero N] (curve : WeierstrassCurve ℤ) :=
  (curve.baseChange ℚ).toAffine.FunctionField →+* gammaZeroFunctionField N

variable {curve : WeierstrassCurve ℤ} {N : ℕ} [NeZero N]

/-- The extension degree of a modular pullback, computed over its image. -/
@[expose] def ModularPullback.degree (pullback : ModularPullback N curve) : ℕ :=
  letI := pullback.toAlgebra
  Module.finrank (curve.baseChange ℚ).toAffine.FunctionField (gammaZeroFunctionField N)

/-- A modular pullback that is onto the modular function field has degree one. -/
theorem ModularPullback.degree_eq_one_of_surjective (pullback : ModularPullback N curve)
    (surjective : Function.Surjective pullback) : pullback.degree = 1 := by
  let := pullback.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr ⟨pullback.injective, surjective⟩

/-- The marked cusp of the modular parametrization maps to the Weierstrass point at infinity. -/
@[expose] def ModularPullback.IsPointed (pullback : ModularPullback N curve) : Prop :=
  (pullback (WeierstrassCurve.Affine.genericX (curve.baseChange ℚ).toAffine)).val
    (CompactifiedQuotient.ofCusp (cuspDatumInftyGammaZero N).cuspOrbit) = ∞

/-- Evaluate a modular function on the upper half-plane, with a dummy zero value at poles. -/
@[expose] def gammaZeroFinitePart (F : gammaZeroFunctionField N) (z : ℍ) : ℂ :=
  F.val.finitePart (CompactifiedQuotient.ofQuotient (Quotient.mk _ z))

/-- The identity `φ*ω_E = c · 2πi f(z) dz` on the open locus where the affine
coordinate functions are finite. The denominator is the standard Weierstrass
invariant differential denominator, so the equality is written after multiplication. -/
@[expose] def ModularPullback.PullsBackDifferential (pullback : ModularPullback N curve)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (c : ℕ) : Prop :=
  let x := pullback (WeierstrassCurve.Affine.genericX (curve.baseChange ℚ).toAffine)
  let y := pullback (WeierstrassCurve.Affine.genericY (curve.baseChange ℚ).toAffine)
  ∀ z : ℍ, let z' := CompactifiedQuotient.ofQuotient (Quotient.mk _ z)
    x.val z' ≠ ∞ → y.val z' ≠ ∞ →
    Derivative.normalizedDerivOfComplex (gammaZeroFinitePart x) z =
      (c : ℂ) * f z * (2 * gammaZeroFinitePart y z +
        (curve.a₁ : ℂ) * gammaZeroFinitePart x z + (curve.a₃ : ℂ))

/-- The integral period image of the scaled newform, generated by traversing all
`Γ₀(N)` loops from a fixed base point. The primitive is normalized at infinity. -/
@[expose] def gammaZeroDifferentialPeriods
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (c : ℕ) : AddSubgroup ℂ :=
  AddSubgroup.closure (Set.range fun γ : gammaZeroEffective N ↦
    (c : ℂ) * (eichlerIntegral 1 1 f (γ • UpperHalfPlane.I) -
      eichlerIntegral 1 1 f UpperHalfPlane.I))

/-- The catalogue codes for a proved binary optimality result. -/
abbrev optimalityStatusCode (optimal : Bool) : ℕ :=
  if optimal then 1 else 0

end VerifiedLcalc.Modularity
