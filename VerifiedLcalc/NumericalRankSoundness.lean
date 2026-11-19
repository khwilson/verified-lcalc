module

public import VerifiedLcalc.NumericalRank
public import VerifiedLcalc.CertificateSoundness
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc

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

/-- Rigorous numerical conclusion. There is deliberately no assertion of exact
vanishing or analytic order in this definition. -/
def SmallDerivatives (f : ℂ → ℂ) (center : ℂ) (n : Nat) (eps : Rat) : Prop :=
  ∀ k < n, |(iteratedDeriv k f center).re| ≤ (eps : ℝ) ∧
    |(iteratedDeriv k f center).im| ≤ (eps : ℝ)

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

/-- The same subject interpretation and true-derivative enclosure obligations
as exact certificates. The numerical policy cannot replace these proofs. -/
structure Evidence (expected : Request) (artifact : Artifact) where
  function : ℂ → ℂ
  denotes : expected.computation.subject.Denotes function
  analytic : AnalyticAt ℂ function (expected.computation.subject.center : ℂ)
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k function (expected.computation.subject.center : ℂ))

theorem check_sound {expected : Request} {artifact : Artifact}
    (evidence : Evidence expected artifact) (h : check expected artifact = true) :
    SmallDerivatives evidence.function (expected.computation.subject.center : ℂ)
      artifact.numericalLowerBound expected.policy.cutoff := by
  obtain ⟨_, _, _, _, _, hlen, hs⟩ := (check_correct _ _).mp h
  rw [← hlen]
  exact enclosures_small _ _ _ evidence.enclosures hs

/-- An explicitly hypothetical separation principle. It is NOT a theorem about
elliptic L-functions, and is never installed as a Lean axiom. A future arithmetic
vanishing theorem may discharge it for the particular function and derivatives. -/
def ExactVanishingHypothesis (f : ℂ → ℂ) (center : ℂ) (n : Nat) (eps : Rat) : Prop :=
  ∀ k < n, (|(iteratedDeriv k f center).re| ≤ (eps : ℝ) ∧
    |(iteratedDeriv k f center).im| ≤ (eps : ℝ)) → iteratedDeriv k f center = 0

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
