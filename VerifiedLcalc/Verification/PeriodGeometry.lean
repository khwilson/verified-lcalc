/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
import TauCeti.Algebra.Module.ZLattice.Complex

/-! # Exact consequences of a checked class area ratio -/

public section

namespace VerifiedLcalc

open scoped Pointwise

/-- The complex period area is positive because the period lattice is full in `ℂ`. -/
theorem complexPeriodArea_pos (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    0 < complexPeriodArea W :=
  ZLattice.covolume_pos _ _

/-- An admissible coordinate change between globally minimal equations preserves area. -/
theorem complexPeriodArea_eq_of_minimal_change {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] {C : WeierstrassCurve.VariableChange ℚ}
    (h₁ : WeierstrassCurve.IsGlobalMinimal ℤ W₁)
    (h₂ : WeierstrassCurve.IsGlobalMinimal ℤ W₂) (hC : C • W₁ = W₂) :
    complexPeriodArea W₂ = complexPeriodArea W₁ := by
  let _ := h₁.isIntegral
  have h₂' : WeierstrassCurve.IsGlobalMinimal ℤ (C • W₁) := by
    simpa only [hC] using h₂
  have hu := (W₁.abs_u_eq_one_iff_isGlobalMinimal h₂').2 h₁
  let c := C.map (Rat.castHom ℂ)
  have hc : ‖(c.u : ℂ)‖ = 1 := by
    change ‖((C.u : ℚ) : ℂ)‖ = 1
    rw [Complex.norm_ratCast, ← Rat.cast_abs, hu, Rat.cast_one]
  let _ : NeZero (c.u : ℂ) := ⟨c.u.ne_zero⟩
  have hmap : c • W₁.map (Rat.castHom ℂ) = W₂.map (Rat.castHom ℂ) :=
    (WeierstrassCurve.map_variableChange _ _ _).trans (congrArg (fun W => W.map (Rat.castHom ℂ)) hC)
  unfold complexPeriodArea
  simp_rw [← hmap]
  rw [WeierstrassCurve.variableChange_periodLattice]
  change ZLattice.covolume ((c.u : ℂ) • (W₁.map (Rat.castHom ℂ)).periodLattice) _ = _
  rw [ZLattice.covolume_complex_smul, hc, one_pow, one_mul]

namespace FaltingsIndexFact

variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]

/-- The zero-based Faltings index is the number of representatives before the input. -/
@[expose] def index (fact : FaltingsIndexFact curve) : ℕ := fact.predecessors.card

open Classical in
/-- The finite witness gives the exact number of predecessors among all class members. -/
theorem index_eq_card_filter (fact : FaltingsIndexFact curve) :
    fact.index = (Finset.univ.filter fun i => faltingsPrecedes (fun j =>
      let _ := fact.model.elliptic j
      catalogueFaltingsHeight (fact.model.representatives j)) i fact.model.curveIndex).card := by
  unfold index
  congr 1
  ext i
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using fact.mem_predecessors i

end FaltingsIndexFact

namespace FaltingsRatioFact

variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]

/-- The claimed numerator is the greatest complex area in the proved class. -/
theorem isGreatest_area (fact : FaltingsRatioFact curve) :
    IsGreatest (Set.range fun i => haveI := fact.model.elliptic i
        complexPeriodArea (fact.model.representatives i))
      ((fact.ratio.val : ℝ) * complexPeriodArea (curve.baseChange ℚ)) := by
  rw [← fact.area_eq]
  refine ⟨⟨fact.maximizingIndex, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact fact.isMaximum i

/-- The claimed natural number is exactly the quotient of maximal and input areas. -/
theorem ratio_eq_div (fact : FaltingsRatioFact curve) :
    haveI := fact.model.elliptic fact.maximizingIndex
    (fact.ratio.val : ℝ) = complexPeriodArea (fact.model.representatives fact.maximizingIndex) /
      complexPeriodArea (curve.baseChange ℚ) := by
  rw [eq_div_iff (complexPeriodArea_pos _).ne']
  exact fact.area_eq.symm

end FaltingsRatioFact

end VerifiedLcalc
