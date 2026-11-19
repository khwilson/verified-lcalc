import VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Lean

/-- Supplied finite/infinite classification makes the `Nat.card` convention
computable; classification itself is not inferred by classical choice. -/
def cardinalityFrom (α : Type*) (data : Fintype α ⊕' Infinite α) : ℕ :=
  match data with
  | .inl finite => @Fintype.card α finite
  | .inr _ => 0

theorem cardinalityFrom_eq_card (α : Type*) (data : Fintype α ⊕' Infinite α) :
    cardinalityFrom α data = Nat.card α := by
  cases data with
  | inl finite => exact @Fintype.card_eq_nat_card α finite
  | inr infinite =>
    let _ := infinite
    exact Nat.card_eq_zero_of_infinite.symm

example : cardinalityFrom (Fin 7) (.inl inferInstance) = 7 := by decide +kernel
example : cardinalityFrom ℕ (.inr inferInstance) = 0 := by decide +kernel

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Singular models at small characteristics must include their singular points.
example : (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve (ZMod 2)).pointCountFinite = 3 := by
  decide +kernel
example : (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve (ZMod 3)).pointCountFinite = 4 := by
  decide +kernel
example : (⟨0, -1, 1, -10, -20⟩ : WeierstrassCurve (ZMod 5)).pointCountFinite = 5 := by
  decide +kernel

-- This identity is proved generally, not just tested on the preceding examples.
#print axioms WeierstrassCurve.pointCountFinite_eq_pointCount
#print axioms cardinalityFrom_eq_card
