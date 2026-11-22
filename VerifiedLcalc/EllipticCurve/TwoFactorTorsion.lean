module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Torsion

/-!
# Torsion from independent cyclic subgroups of orders two and n

A checked point of order two contributes a distinct factor when it lies outside
the cyclic subgroup of the second point. A matching upper bound then proves the
sum of the two cyclic subgroups is the whole torsion subgroup.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

variable {A : Type*} [AddCommGroup A] {P Q : A} {n : ℕ}

/-- Test the natural multiples of the second point up to its supplied order. -/
def outsideCyclicCheck [DecidableEq A] (P Q : A) (n : ℕ) : Bool :=
  (List.range n).all (fun k => decide (k • Q ≠ P))

/-- When the second point has positive order `n`, those multiples cover its cyclic subgroup. -/
theorem outsideCyclicCheck_sound [DecidableEq A] (hn : 0 < n) (hQ : addOrderOf Q = n)
    (h : outsideCyclicCheck P Q n = true) : P ∉ AddSubgroup.zmultiples Q := by
  intro hmem
  have hfin := addOrderOf_pos_iff.mp (hQ.symm ▸ hn)
  obtain ⟨k, hk, hkp⟩ := Finset.mem_image.mp (hfin.mem_zmultiples_iff_mem_range_addOrderOf.mp hmem)
  have hk' : k < n := hQ ▸ Finset.mem_range.mp hk
  exact of_decide_eq_true (List.all_eq_true.mp h k (List.mem_range.mpr hk')) hkp

private theorem disjoint_zmultiples_of_order_two (hP : addOrderOf P = 2)
    (hout : P ∉ AddSubgroup.zmultiples Q) :
    Disjoint (AddSubgroup.zmultiples P) (AddSubgroup.zmultiples Q) := by
  classical
  apply AddSubgroup.disjoint_def.mpr
  intro x hxP hxQ
  have hfin := addOrderOf_pos_iff.mp (hP.symm ▸ (by decide : 0 < (2 : ℕ)))
  obtain ⟨k, hk, hkp⟩ := Finset.mem_image.mp (hfin.mem_zmultiples_iff_mem_range_addOrderOf.mp hxP)
  have hk' : k < 2 := hP ▸ Finset.mem_range.mp hk
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · simpa only [zero_nsmul] using hkp.symm
  · exact (hout ((by simpa only [one_nsmul] using hkp : P = x).symm ▸ hxQ)).elim

private noncomputable def zmodEquivMultiples {G : Type*} [AddGroup G] (P : G) {n : ℕ}
    (hP : addOrderOf P = n) : ZMod n ≃+ AddSubgroup.zmultiples P := by
  let generator : AddSubgroup.zmultiples P := ⟨P, AddSubgroup.mem_zmultiples P⟩
  apply zmodAddEquivOfGenerator (g := generator)
  · intro x
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, Subtype.ext hk⟩
  · exact (Nat.card_zmultiples P).trans hP

private theorem zmodEquivMultiples_one {G : Type*} [AddGroup G] (P : G) {n : ℕ}
    (hP : addOrderOf P = n) : (zmodEquivMultiples P hP 1 : G) = P := by
  unfold zmodEquivMultiples
  rw [zmodAddEquivOfGenerator_apply_one]

/-- An order-two point outside the subgroup of an order-`n` point gives the
claimed product structure when `2 * n` is also a divisor bound for the full group. -/
theorem exists_torsion_addEquiv_two_factor (hn : 0 < n) (hP : addOrderOf P = 2)
    (hQ : addOrderOf Q = n) (hout : P ∉ AddSubgroup.zmultiples Q)
    (hbound : Nat.card (AddCommGroup.torsion A) ∣ 2 * n) :
    ∃ e : ZMod 2 × ZMod n ≃+ AddCommGroup.torsion A,
      (e (1, 0) : A) = P ∧ (e (0, 1) : A) = Q := by
  let torsion := AddCommGroup.torsion A
  have hmemP : P ∈ torsion :=
    (AddCommGroup.mem_torsion P).mpr (addOrderOf_pos_iff.mp (hP.symm ▸ (by decide)))
  have hmemQ : Q ∈ torsion :=
    (AddCommGroup.mem_torsion Q).mpr (addOrderOf_pos_iff.mp (hQ.symm ▸ hn))
  let p : torsion := ⟨P, hmemP⟩
  let q : torsion := ⟨Q, hmemQ⟩
  have hp : addOrderOf p = 2 := (AddSubgroup.addOrderOf_mk P hmemP).trans hP
  have hq : addOrderOf q = n := (AddSubgroup.addOrderOf_mk Q hmemQ).trans hQ
  have hd : Disjoint (AddSubgroup.zmultiples p) (AddSubgroup.zmultiples q) := by
    apply disjoint_zmultiples_of_order_two hp
    intro h
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
    exact hout (AddSubgroup.mem_zmultiples_iff.mpr ⟨k, congrArg Subtype.val hk⟩)
  let sum := (AddSubgroup.zmultiples p).subtype.coprod (AddSubgroup.zmultiples q).subtype
  have hsum : Function.Injective sum := AddSubgroup.add_injective_of_disjoint hd
  have hpos : 0 < 2 * n := Nat.mul_pos (by decide) hn
  let : Finite torsion := Nat.finite_of_card_ne_zero (by
    intro hzero
    change Nat.card torsion ∣ 2 * n at hbound
    rw [hzero, zero_dvd_iff] at hbound
    exact hpos.ne' hbound)
  have hle : Nat.card torsion ≤ Nat.card (AddSubgroup.zmultiples p × AddSubgroup.zmultiples q) := by
    rw [Nat.card_prod, Nat.card_zmultiples, hp, Nat.card_zmultiples, hq]
    exact Nat.le_of_dvd hpos hbound
  let summation := AddEquiv.ofBijective sum (hsum.bijective_of_nat_card_le hle)
  let e := ((zmodEquivMultiples p hp).prodCongr (zmodEquivMultiples q hq)).trans summation
  refine ⟨e, ?_, ?_⟩
  · change (((zmodEquivMultiples p hp 1 : torsion) + (zmodEquivMultiples q hq 0 : torsion)) : A) = P
    simp only [map_zero, AddSubgroup.coe_zero, add_zero, zmodEquivMultiples_one]
    rfl
  · change (((zmodEquivMultiples p hp 0 : torsion) + (zmodEquivMultiples q hq 1 : torsion)) : A) = Q
    simp only [map_zero, AddSubgroup.coe_zero, zero_add, zmodEquivMultiples_one]
    rfl

end VerifiedLcalc.EllipticCurve
