/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
public import Mathlib.Data.ZMod.Basic

/-! # Torsion projections and generation from checked subgroup presentations -/

@[expose] public section

export VerifiedLcalc (instReprTorsionBoundWitness instDecidableEqTorsionBoundWitness)

namespace VerifiedLcalc

/-- The checked positive multiple of the full torsion order. -/
def TorsionDivisorFacts.bound {curve : WeierstrassCurve ℤ}
    (facts : TorsionDivisorFacts curve) : ℕ :=
  facts.evidence.bound

namespace Certification

variable {A : Type*} [AddCommGroup A] {S : AddSubgroup A} {t : Set A} {m n : ℕ}

/-- The image of one under a cyclic presentation generates the target subgroup. -/
theorem closure_eq_of_cyclic_presentation (e : ZMod n ≃+ S) (ht : t ⊆ S)
    (h1 : (e 1 : A) ∈ AddSubgroup.closure t) : AddSubgroup.closure t = S := by
  refine le_antisymm ((AddSubgroup.closure_le _).mpr ht) ?_
  intro x hx
  obtain ⟨v, hv⟩ := e.surjective ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective v
  let f := S.subtype.comp e.toAddMonoidHom
  have he : k • f 1 = x := by
    rw [← map_zsmul, zsmul_one]
    exact congrArg Subtype.val hv
  exact he ▸ (AddSubgroup.closure t).zsmul_mem h1 k

/-- The two standard generators of a product presentation generate the target subgroup. -/
theorem closure_eq_of_twoFactor_presentation (e : ZMod m × ZMod n ≃+ S) (ht : t ⊆ S)
    (h1 : (e (1, 0) : A) ∈ AddSubgroup.closure t)
    (h2 : (e (0, 1) : A) ∈ AddSubgroup.closure t) : AddSubgroup.closure t = S := by
  refine le_antisymm ((AddSubgroup.closure_le _).mpr ht) ?_
  intro x hx
  obtain ⟨⟨u, v⟩, hv⟩ := e.surjective ⟨x, hx⟩
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective u
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective v
  let f := S.subtype.comp e.toAddMonoidHom
  have hij : j • (1, 0) + k • (0, 1) = ((j : ZMod m), (k : ZMod n)) := by
    ext <;> simp
  have he : j • f (1, 0) + k • f (0, 1) = x := by
    rw [← map_zsmul, ← map_zsmul, ← map_add, hij]
    exact congrArg Subtype.val hv
  exact he ▸ (AddSubgroup.closure t).add_mem
    ((AddSubgroup.closure t).zsmul_mem h1 j) ((AddSubgroup.closure t).zsmul_mem h2 k)

end Certification

end VerifiedLcalc
