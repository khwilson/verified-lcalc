module

public import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.TypeStar

/-!
# Exact cyclic torsion from a point order and an upper divisor

The input divisor bound concerns the full torsion subgroup of a commutative group.
An element whose exact order attains that bound generates the whole torsion subgroup.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

variable {A : Type*} [CommGroup A] {P : A} {n : ℕ}

/-- If an element has positive order `n` and the torsion subgroup's order divides `n`,
then the torsion subgroup has exactly `n` elements. -/
@[to_additive torsion_card_eq_of_order_dvd]
theorem mul_torsion_card_eq_of_order_dvd (hn : 0 < n) (hP : orderOf P = n)
    (hbound : Nat.card (CommGroup.torsion A) ∣ n) :
    Nat.card (CommGroup.torsion A) = n := by
  have hmem : P ∈ CommGroup.torsion A :=
    (CommGroup.mem_torsion P).mpr (orderOf_pos_iff.mp (hP.symm ▸ hn))
  let point : CommGroup.torsion A := ⟨P, hmem⟩
  have horder : orderOf point = n := (Subgroup.orderOf_mk P hmem).trans hP
  exact Nat.dvd_antisymm hbound (horder ▸ orderOf_dvd_natCard point)

/-- A point of order equal to an upper divisor generates the whole torsion subgroup. -/
@[to_additive]
theorem torsion_eq_zpowers_of_order_dvd (hn : 0 < n) (hP : orderOf P = n)
    (hbound : Nat.card (CommGroup.torsion A) ∣ n) :
    Subgroup.zpowers (⟨P, (CommGroup.mem_torsion P).mpr
      (orderOf_pos_iff.mp (hP.symm ▸ hn))⟩ : CommGroup.torsion A) = ⊤ := by
  have hmem : P ∈ CommGroup.torsion A :=
    (CommGroup.mem_torsion P).mpr (orderOf_pos_iff.mp (hP.symm ▸ hn))
  let point : CommGroup.torsion A := ⟨P, hmem⟩
  have horder : orderOf point = n := (Subgroup.orderOf_mk P hmem).trans hP
  have hcard := mul_torsion_card_eq_of_order_dvd hn hP hbound
  have hcyclic : Nat.card (Subgroup.zpowers point) = n := by
    rw [Nat.card_zpowers, horder]
  let : Finite (Subgroup.zpowers point) :=
    Nat.finite_of_card_ne_zero (hcyclic.symm ▸ hn.ne')
  exact Subgroup.eq_top_of_card_eq _ (hcyclic.trans hcard.symm)

/-- A point of order equal to the upper divisor determines a multiplicative
isomorphism from `Multiplicative (ZMod n)` to the whole torsion subgroup mapping
`Multiplicative.ofAdd 1` to the given element. -/
theorem exists_torsion_mulEquiv_of_order_dvd (hn : 0 < n) (hP : orderOf P = n)
    (hbound : Nat.card (CommGroup.torsion A) ∣ n) :
    ∃ e : Multiplicative (ZMod n) ≃* CommGroup.torsion A,
      (e (Multiplicative.ofAdd 1) : A) = P := by
  have hmem : P ∈ CommGroup.torsion A :=
    (CommGroup.mem_torsion P).mpr (orderOf_pos_iff.mp (hP.symm ▸ hn))
  let point : CommGroup.torsion A := ⟨P, hmem⟩
  have hgen : ∀ x : CommGroup.torsion A, x ∈ Subgroup.zpowers point :=
    (Subgroup.eq_top_iff' _).mp (torsion_eq_zpowers_of_order_dvd hn hP hbound)
  have hcard := mul_torsion_card_eq_of_order_dvd hn hP hbound
  refine ⟨zmodMulEquivOfGenerator hgen hcard, ?_⟩
  change ((zmodMulEquivOfGenerator hgen hcard (Multiplicative.ofAdd 1) :
    CommGroup.torsion A) : A) = P
  rw [zmodMulEquivOfGenerator_apply_ofAdd_one]

/-- A point of order equal to the upper divisor determines an additive isomorphism
from `ZMod n` to the whole torsion subgroup mapping `1` to the given point. -/
theorem exists_torsion_addEquiv_of_order_dvd {A : Type*} [AddCommGroup A] {P : A} {n : ℕ}
    (hn : 0 < n) (hP : addOrderOf P = n)
    (hbound : Nat.card (AddCommGroup.torsion A) ∣ n) :
    ∃ e : ZMod n ≃+ AddCommGroup.torsion A, (e 1 : A) = P := by
  have hmem : P ∈ AddCommGroup.torsion A :=
    (AddCommGroup.mem_torsion P).mpr (addOrderOf_pos_iff.mp (hP.symm ▸ hn))
  let point : AddCommGroup.torsion A := ⟨P, hmem⟩
  have hgen : ∀ x : AddCommGroup.torsion A, x ∈ AddSubgroup.zmultiples point :=
    (AddSubgroup.eq_top_iff' _).mp (torsion_eq_zmultiples_of_order_dvd hn hP hbound)
  have hcard := torsion_card_eq_of_order_dvd hn hP hbound
  refine ⟨zmodAddEquivOfGenerator hgen hcard, ?_⟩
  change ((zmodAddEquivOfGenerator hgen hcard 1 : AddCommGroup.torsion A) : A) = P
  rw [zmodAddEquivOfGenerator_apply_one]

end VerifiedLcalc.EllipticCurve
