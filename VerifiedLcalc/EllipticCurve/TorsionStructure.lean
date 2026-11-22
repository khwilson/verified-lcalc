module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Torsion

/-!
# Exact cyclic torsion from a point order and an upper divisor

The input divisor bound concerns the full torsion subgroup of an additive commutative group.
An element whose exact order attains that bound generates the whole torsion subgroup.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

variable {A : Type*} [AddCommGroup A] {P : A} {n : ℕ}

/-- If a point has positive order `n` and the torsion subgroup's order divides `n`,
then the torsion subgroup has exactly `n` elements. -/
theorem torsion_card_eq_of_order_dvd (hn : 0 < n) (hP : addOrderOf P = n)
    (hbound : Nat.card (AddCommGroup.torsion A) ∣ n) :
    Nat.card (AddCommGroup.torsion A) = n := by
  have hmem : P ∈ AddCommGroup.torsion A :=
    (AddCommGroup.mem_torsion P).mpr (addOrderOf_pos_iff.mp (hP.symm ▸ hn))
  let point : AddCommGroup.torsion A := ⟨P, hmem⟩
  have horder : addOrderOf point = n := (AddSubgroup.addOrderOf_mk P hmem).trans hP
  exact Nat.dvd_antisymm hbound (horder ▸ addOrderOf_dvd_natCard point)

/-- A point of order equal to the upper divisor determines an additive isomorphism
from `ZMod n` to the whole torsion subgroup mapping `1` to the given point. -/
theorem exists_torsion_addEquiv_of_order_dvd (hn : 0 < n) (hP : addOrderOf P = n)
    (hbound : Nat.card (AddCommGroup.torsion A) ∣ n) :
    ∃ e : ZMod n ≃+ AddCommGroup.torsion A, (e 1 : A) = P := by
  have hmem : P ∈ AddCommGroup.torsion A :=
    (AddCommGroup.mem_torsion P).mpr (addOrderOf_pos_iff.mp (hP.symm ▸ hn))
  let point : AddCommGroup.torsion A := ⟨P, hmem⟩
  have horder : addOrderOf point = n := (AddSubgroup.addOrderOf_mk P hmem).trans hP
  have hcard := torsion_card_eq_of_order_dvd hn hP hbound
  have hcyclic : Nat.card (AddSubgroup.zmultiples point) = n := by
    rw [Nat.card_zmultiples, horder]
  let : Finite (AddSubgroup.zmultiples point) :=
    Nat.finite_of_card_ne_zero (hcyclic.symm ▸ hn.ne')
  have htop := AddSubgroup.eq_top_of_card_eq _ (hcyclic.trans hcard.symm)
  have hgen (x : AddCommGroup.torsion A) : x ∈ AddSubgroup.zmultiples point :=
    (AddSubgroup.eq_top_iff' _).mp htop x
  refine ⟨zmodAddEquivOfGenerator hgen hcard, ?_⟩
  rw [zmodAddEquivOfGenerator_apply_one]

end VerifiedLcalc.EllipticCurve
