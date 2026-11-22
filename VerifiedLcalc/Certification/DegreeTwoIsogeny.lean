/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificates.DegreeTwoIsogeny
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-! # Certified minimum degree-two isogenies of rational elliptic curves -/

public section

namespace VerifiedLcalc
open TauCeti WeierstrassCurve

/-- Distinct j-invariants rule out a degree-one rational isogeny. -/
theorem two_le_degree_of_j_ne {W V : WeierstrassCurve ℚ} [W.IsElliptic] [V.IsElliptic]
    (hj : W.j ≠ V.j) (φ : Isogeny W.toAffine V.toAffine) : 2 ≤ φ.degree := by
  have hpos := φ.degree_pos
  by_contra h
  have hdeg : φ.degree = 1 := by omega
  obtain ⟨C, hC, _⟩ := φ.exists_variableChangeIsogeny_eq_of_degree_eq_one hdeg
  have he : C • W = V := hC
  subst V
  exact hj (variableChange_j W C).symm

/-- Verify a degree-two edge using a supplied rational kernel and change of target variables. -/
noncomputable def DegreeTwoIsogenyFact.ofVelu (source target : WeierstrassCurve ℤ)
    [(source.baseChange ℚ).IsElliptic] [(target.baseChange ℚ).IsElliptic]
    (Φ : AddSubgroup (((source.baseChange ℚ).toAffine.baseChange ℚ).toAffine.Point))
    [Finite Φ] (hcard : Nat.card Φ = 2)
    (C : VariableChange ℚ) (hC :
      C • (Affine.veluCurve (source.baseChange ℚ).toAffine Φ).toAffine =
        (target.baseChange ℚ).toAffine)
    (hj : (source.baseChange ℚ).j ≠ (target.baseChange ℚ).j) :
    DegreeTwoIsogenyFact source target where
  source_elliptic := inferInstance
  target_elliptic := inferInstance
  isogeny := (Isogeny.variableChangeIsogeny C hC).comp (Affine.veluIsogeny _ Φ)
  degree_eq := by
    rw [Isogeny.degree_comp, Isogeny.degree_variableChangeIsogeny, Affine.degree_veluIsogeny,
      hcard, one_mul]
  kernel_card := by
    let φ := Affine.veluIsogeny (source.baseChange ℚ).toAffine Φ
    let ψ := Isogeny.variableChangeIsogeny C hC
    have hφ : φ.ker = Φ := Affine.ker_veluIsogeny (source.baseChange ℚ).toAffine Φ
    have hsub : Φ ≤ (ψ.comp φ).ker :=
      (le_of_eq hφ.symm).trans (Isogeny.ker_le_ker_comp ψ φ)
    have hlo : Nat.card Φ ≤ Nat.card (ψ.comp φ).ker :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    have hhi := (ψ.comp φ).card_ker_le_degree
    have hdeg : (ψ.comp φ).degree = 2 := by
      rw [Isogeny.degree_comp, Isogeny.degree_variableChangeIsogeny,
        Affine.degree_veluIsogeny, hcard, one_mul]
    rw [hcard] at hlo
    rw [hdeg] at hhi
    exact le_antisymm hhi hlo
  degree_le := two_le_degree_of_j_ne hj

/-- The exhibited edge has a cyclic rational kernel. -/
theorem DegreeTwoIsogenyFact.kernel_cyclic {source target : WeierstrassCurve ℤ}
    (fact : DegreeTwoIsogenyFact source target) :
    letI := fact.source_elliptic
    IsAddCyclic fact.isogeny.ker := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact isAddCyclic_of_prime_card fact.kernel_card

end VerifiedLcalc
