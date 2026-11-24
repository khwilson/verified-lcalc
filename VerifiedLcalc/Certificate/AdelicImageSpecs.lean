/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Basic
public import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus

/-! # Integral adelic images and their modular curves

The adelic group uses the product over rational primes of integral local matrix groups.
At a modulus `N` its reduction is written in the prime-power coordinates of the Chinese
remainder theorem. The associated analytic curve is the compactified quotient of the
effective projective image of the determinant-one integral pullback.
-/

@[expose] public section

namespace VerifiedLcalc

open scoped MatrixGroups
open Matrix

/-- Give the padic ring its prime instance from the type of rational primes. -/
abbrev AdelicLocalRing (p : Nat.Primes) : Type :=
  letI : Fact p.val.Prime := ⟨p.property⟩
  ℤ_[p.val]

/-- The integral adelic general linear group in local coordinates. -/
abbrev AdelicGL : Type := (p : Nat.Primes) → GeneralLinearGroup (Fin 2) (AdelicLocalRing p)

/-- The reduction to each prime-power factor of a positive modulus. -/
noncomputable def adelicPrimePowerReduction (N : ℕ+) : AdelicGL →*
    ((p : (N : ℕ).primeFactors) → GeneralLinearGroup (Fin 2)
      (ZMod (p.val ^ (N : ℕ).factorization p.val))) where
  toFun g p :=
    letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    GeneralLinearGroup.map (PadicInt.toZModPow ((N : ℕ).factorization p.val))
      (g ⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩)
  map_one' := by
    funext p
    exact map_one _
  map_mul' g h := by
    funext p
    exact map_mul _ _ _

/-- The Chinese remainder equivalence on general linear groups. -/
noncomputable def adelicCRT (N : ℕ+) : GeneralLinearGroup (Fin 2) (ZMod (N : ℕ)) ≃*
    ((p : (N : ℕ).primeFactors) → GeneralLinearGroup (Fin 2)
      (ZMod (p.val ^ (N : ℕ).factorization p.val))) :=
  (GeneralLinearGroup.mapEquiv (Fin 2) (ZMod.equivPi (N : ℕ) N.ne_zero)).trans
    (GeneralLinearGroup.piEquiv
      (fun p : (N : ℕ).primeFactors => ZMod (p.val ^ (N : ℕ).factorization p.val)))

/-- The standard reduction of the integral adelic matrix group modulo a positive integer. -/
noncomputable def adelicReduction (N : ℕ+) :
    AdelicGL →* GeneralLinearGroup (Fin 2) (ZMod (N : ℕ)) :=
  (adelicCRT N).symm.toMonoidHom.comp (adelicPrimePowerReduction N)

/-- Diagonal embedding of the determinant-one integral group in the adelic group. -/
noncomputable def adelicSL2 : SL(2, ℤ) →* AdelicGL where
  toFun g p :=
    letI : Fact p.val.Prime := ⟨p.property⟩
    Matrix.SpecialLinearGroup.mapGL (AdelicLocalRing p) g
  map_one' := by
    funext p
    exact map_one _
  map_mul' g h := by
    funext p
    exact map_mul _ g h

/-- The congruence pullback consisting of determinant-one integral matrices in the adelic image. -/
noncomputable def adelicCongruenceSubgroup (H : Subgroup AdelicGL) : Subgroup SL(2, ℤ) :=
  H.comap adelicSL2

/-- The effective modular subgroup. The map to the projective group identifies the two signs,
as required for the coarse modular curve even when the adelic image omits `-I`. -/
noncomputable def adelicProjectiveSubgroup (H : Subgroup AdelicGL) : Subgroup PSL(2, ℝ) :=
  (adelicCongruenceSubgroup H).map sl2zToPSL2R

/-- The effective image of the integral modular subgroup is discrete. -/
instance (H : Subgroup AdelicGL) : DiscreteTopology (adelicProjectiveSubgroup H) := by
  unfold adelicProjectiveSubgroup
  infer_instance

/-- The native incomplete LMFDB label with the conjugacy-class suffix unspecified. -/
def formatPartialAdelicImage (level index genus : ℕ) : String :=
  s!"{level}.{index}.{genus}.?"

end VerifiedLcalc
