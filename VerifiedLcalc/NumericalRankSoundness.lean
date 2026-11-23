/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.NumericalRank
public import VerifiedLcalc.CertificateSoundness
public import VerifiedLcalc.Certificate.Witnesses.Analytic
public import Mathlib.Tactic.Linarith

/-! Soundness theorems for numerical derivative observations. -/

@[expose] public section

namespace VerifiedLcalc

/-- Every point in a box passing the cutoff test has both components bounded in absolute value. -/
theorem Box.withinCutoff_sound {b : Box} {eps : Rat} {z : ℂ}
    (h : b.withinCutoff eps = true) (hz : b.Contains z) :
    |z.re| ≤ (eps : ℝ) ∧ |z.im| ≤ (eps : ℝ) := by
  obtain ⟨_, _, _, hrl, hrh, hil, hih⟩ := (b.withinCutoff_correct eps).mp h
  have hrl' : -(eps : ℝ) ≤ (b.reLo : ℝ) := by exact_mod_cast hrl
  have hrh' : (b.reHi : ℝ) ≤ (eps : ℝ) := by exact_mod_cast hrh
  have hil' : -(eps : ℝ) ≤ (b.imLo : ℝ) := by exact_mod_cast hil
  have hih' : (b.imHi : ℝ) ≤ (eps : ℝ) := by exact_mod_cast hih
  exact ⟨abs_le.mpr ⟨hrl'.trans hz.1.1, hz.1.2.trans hrh'⟩,
    abs_le.mpr ⟨hil'.trans hz.2.1, hz.2.2.trans hih'⟩⟩

namespace NumericalRanks

/-- Every enclosed derivative within a cutoff satisfies its coordinatewise bound. -/
theorem enclosures_small (bs : List Box) (a : Nat → ℂ) (eps : Rat)
    (he : Encloses bs a)
    (hs : ∀ b ∈ bs, b.withinCutoff eps = true) :
    ∀ k < bs.length, |(a k).re| ≤ (eps : ℝ) ∧ |(a k).im| ≤ (eps : ℝ) := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    intro k hk
    cases k with
    | zero => exact b.withinCutoff_sound (hs b (by simp)) he.1
    | succ k =>
      exact ih (fun j => a (j + 1)) he.2
        (fun b hb => hs b (by simp [hb])) k (by simpa using hk)

/-- The finite checker and analytic evidence imply coordinatewise smallness. -/
theorem check_sound {expected : Request} {artifact : Artifact}
    (evidence : Evidence expected artifact) (h : check expected artifact = true) :
    SmallDerivatives evidence.function (expected.computation.subject.center : ℂ)
      artifact.numericalLowerBound expected.policy.cutoff := by
  obtain ⟨_, _, _, _, _, hlen, hs⟩ := (check_correct _ _).mp h
  rw [← hlen]
  exact enclosures_small _ _ _ evidence.enclosures hs

/-- A genuine analytic-rank lower bound, conditional on the displayed additional
mathematical hypothesis. The smallness certificate alone cannot prove it. -/
theorem check_conditional_lowerBound {expected : Request} {artifact : Artifact}
    (evidence : Evidence expected artifact) (h : check expected artifact = true)
    (hvanish : ExactVanishingHypothesis evidence.function
      (expected.computation.subject.center : ℂ) artifact.numericalLowerBound
      expected.policy.cutoff) :
    (artifact.numericalLowerBound : ℕ∞) ≤
      analyticOrderAt evidence.function (expected.computation.subject.center : ℂ) := by
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero evidence.analytic).mpr
  intro k hk
  exact hvanish k hk (check_sound evidence h k hk)

end NumericalRanks
end VerifiedLcalc
