/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Isogeny
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-! # Certified minimum degree-two isogenies of rational elliptic curves -/

public section

namespace VerifiedLcalc
open TauCeti WeierstrassCurve

/-- A degree-two edge between the specified rational equations, with its minimum-degree proof. -/
structure DegreeTwoIsogenyFact (source target : WeierstrassCurve ℤ) where
  /-- Nonsingularity of the rational source curve. -/
  source_elliptic : (source.baseChange ℚ).IsElliptic
  /-- Nonsingularity of the rational target curve. -/
  target_elliptic : (target.baseChange ℚ).IsElliptic
  /-- Rational isogeny between the two supplied equations. -/
  isogeny : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine
  /-- The exhibited isogeny has degree two. -/
  degree_eq : isogeny.degree = 2
  /-- The rational kernel has both points and has cardinality two. -/
  kernel_card : letI := source_elliptic
    Nat.card isogeny.ker = 2
  /-- Every rational isogeny between these equations has degree at least two. -/
  degree_le : ∀ φ : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine,
    2 ≤ φ.degree

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

/-- Two is the attained minimum of all rational isogeny degrees in this direction. -/
theorem DegreeTwoIsogenyFact.isLeast_degree {source target : WeierstrassCurve ℤ}
    (fact : DegreeTwoIsogenyFact source target) :
    IsLeast (Set.range fun φ :
      Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine => φ.degree) 2 := by
  refine ⟨⟨fact.isogeny, fact.degree_eq⟩, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact fact.degree_le φ

end VerifiedLcalc
