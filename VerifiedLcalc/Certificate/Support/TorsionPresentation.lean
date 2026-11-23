/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
import Mathlib.Algebra.Ring.Fin
import Mathlib.Tactic.FinCases

/-! # Generator-preserving presentations of the rational torsion subgroup -/

@[expose] public section

namespace VerifiedLcalc.TorsionPresentation

variable {curve : WeierstrassCurve ℚ} {r : ℕ} (source : Fin r → curve.toAffine.Point)

/-- A subgroup of cardinality one has an empty family of invariant factors. -/
def ofTrivial (h : Nat.card (AddCommGroup.torsion curve.toAffine.Point) = 1) :
    TorsionPresentation source where
  k := 0
  factor := Fin.elim0
  factor_nontrivial i := i.elim0
  factors_divide i := i.elim0
  indices := Fin.elim0
  realization := by
    let := (Nat.card_eq_one_iff_unique.mp h).1
    let : Unique (AddCommGroup.torsion curve.toAffine.Point) :=
      ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    exact ⟨AddEquiv.ofUnique, fun j => j.elim0⟩

/-- Present cyclic torsion by the single invariant factor whose standard generator maps to
the indicated submitted point. -/
def ofCyclic (i : Fin r) (n : ℕ) (hn : 1 < n)
    (h : ∃ e : ZMod n ≃+ AddCommGroup.torsion curve.toAffine.Point,
      (e 1 : curve.toAffine.Point) = source i) : TorsionPresentation source where
  k := 1
  factor := fun _ => n
  factor_nontrivial _ := hn
  factors_divide _ _ _ := dvd_rfl
  indices := fun _ => i
  realization := by
    obtain ⟨e, he⟩ := h
    refine ⟨(AddEquiv.funUnique (Fin 1) (ZMod n)).trans e, ?_⟩
    intro j
    fin_cases j
    simpa [AddEquiv.funUnique, Equiv.funUnique, Equiv.piUnique] using he

/-- Present two-factor torsion with both cyclic factors matched to the submitted points. -/
def ofTwoFactor (i j : Fin r) (n : ℕ) (hn : 1 < n) (hdvd : 2 ∣ n)
    (h : ∃ e : ZMod 2 × ZMod n ≃+ AddCommGroup.torsion curve.toAffine.Point,
      (e (1, 0) : curve.toAffine.Point) = source i ∧
      (e (0, 1) : curve.toAffine.Point) = source j) : TorsionPresentation source where
  k := 2
  factor := ![2, n]
  factor_nontrivial a := by fin_cases a <;> first | exact hn | exact (by decide : 1 < 2)
  factors_divide a b hab := by
    fin_cases a <;> fin_cases b <;> first
    | exact hdvd
    | exact dvd_rfl
    | exact ((by decide : ¬ (1 : Fin 2) < 0) hab).elim
  indices := ![i, j]
  realization := by
    obtain ⟨e, hP, hQ⟩ := h
    let R := fun a : Fin 2 => ZMod (![2, n] a)
    refine ⟨(RingEquiv.piFinTwo R).toAddEquiv.trans e, ?_⟩
    intro a
    fin_cases a
    · change (e _ : curve.toAffine.Point) = source i
      rw [← hP]
      apply congrArg fun t : ZMod 2 × ZMod n => (e t : curve.toAffine.Point)
      exact Prod.ext (Pi.single_eq_same (M := R) (0 : Fin 2) 1)
        (Pi.single_eq_of_ne (M := R) (by decide : (1 : Fin 2) ≠ 0) 1)
    · change (e _ : curve.toAffine.Point) = source j
      rw [← hQ]
      apply congrArg fun t : ZMod 2 × ZMod n => (e t : curve.toAffine.Point)
      exact Prod.ext (Pi.single_eq_of_ne (M := R) (by decide : (0 : Fin 2) ≠ 1) 1)
        (Pi.single_eq_same (M := R) (1 : Fin 2) 1)

end VerifiedLcalc.TorsionPresentation
