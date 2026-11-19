module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.Numerics
open Set MeasureTheory Filter

/-- Split the central Mellin integral at one using the weight-two inversion
identity. This theorem is independent of elliptic curves and of all custom axioms. -/
theorem mellin_one_split (f : ℝ → ℂ) (w : ℂ) (hf : MellinConvergent f 1)
    (hfeq : ∀ t : ℝ, 0 < t → f (1 / t) = w * (t : ℂ) ^ 2 * f t) :
    mellin f 1 = (1 + w) * mellin ((Ioi (1 : ℝ)).indicator f) 1 := by
  let low := (Ioo (0 : ℝ) 1).indicator f
  let high := (Ioi (1 : ℝ)).indicator f
  have hInt : IntegrableOn f (Ioi 0) := by simpa [MellinConvergent] using hf
  have hl : IntegrableOn low (Ioi 0) := hInt.indicator measurableSet_Ioo
  have hh : IntegrableOn high (Ioi 0) := hInt.indicator measurableSet_Ioi
  have hsum : (∫ t : ℝ in Ioi 0, f t) =
      (∫ t : ℝ in Ioi 0, low t) + (∫ t : ℝ in Ioi 0, high t) := by
    rw [← integral_add hl hh]
    apply integral_congr_ae
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := volume.ae_ne 1
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hne] with t ht hne
    rcases lt_or_gt_of_ne hne with h | h
    · change f t = low t + high t
      dsimp [low, high]
      rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, h⟩),
        indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr h.le)]
      simp
    · dsimp [low, high]
      rw [indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun hm => not_lt_of_ge h.le hm.2),
        indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h)]
      simp
  have hlow : mellin low 1 = w * mellin high 1 := by
    have he : ∀ t ∈ Ioi (0 : ℝ),
        low t = w * ((t : ℂ) ^ (-2 : ℂ) * high t⁻¹) := by
      intro t ht
      by_cases h : t < 1
      · have hi : 1 < t⁻¹ := (one_lt_inv₀ ht).mpr h
        have hfe := hfeq t⁻¹ (inv_pos.mpr ht)
        simp only [one_div, inv_inv] at hfe
        dsimp [low, high]
        rw [indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, h⟩),
          indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from hi)]
        simpa [Complex.cpow_neg, inv_pow, mul_assoc] using hfe
      · have hi : ¬ 1 < t⁻¹ := by
          exact not_lt.mpr ((inv_le_one₀ ht).mpr (le_of_not_gt h))
        simp [low, high, h, hi]
    calc
      mellin low 1 = mellin (fun t : ℝ => w • ((t : ℂ) ^ (-2 : ℂ) • high t⁻¹)) 1 := by
        unfold mellin
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa only [sub_self, Complex.cpow_zero, one_smul, smul_eq_mul, one_mul] using he t ht
      _ = w * mellin (fun t : ℝ => (t : ℂ) ^ (-2 : ℂ) • high t⁻¹) 1 :=
        mellin_const_smul _ _ w
      _ = w * mellin high 1 := by
        rw [mellin_cpow_smul, mellin_comp_inv]
        norm_num
  have hl' : (∫ t : ℝ in Ioi 0, low t) = w * (∫ t : ℝ in Ioi 0, high t) := by
    simpa [mellin] using hlow
  simp only [mellin, sub_self, Complex.cpow_zero, one_smul]
  rw [hsum, hl']
  dsimp [high]
  ring

end VerifiedLcalc.Numerics
