module

public import VerifiedLcalc.Scan
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

namespace VerifiedLcalc

/-- A complex number lies in the closed coordinate intervals given by the
rational endpoints. Interval semantics come from mathlib's `Set.Icc`. -/
def Box.Contains (b : Box) (z : ℂ) : Prop :=
  z.re ∈ Set.Icc (b.reLo : ℝ) (b.reHi : ℝ) ∧
    z.im ∈ Set.Icc (b.imLo : ℝ) (b.imHi : ℝ)

theorem Box.isZero_sound {b : Box} {z : ℂ}
    (h : b.isZero = true) (hz : b.Contains z) : z = 0 := by
  obtain ⟨hrl, hrh, hil, hih⟩ := b.isZero_correct.mp h
  simp only [Contains, hrl, hrh, hil, hih, Rat.cast_zero,
    Set.Icc_self, Set.mem_singleton_iff] at hz
  exact Complex.ext hz.1 hz.2

theorem Box.excludesZero_sound {b : Box} {z : ℂ}
    (h : b.excludesZero = true) (hz : b.Contains z) : z ≠ 0 := by
  intro heq
  subst z
  obtain ⟨⟨hrl, hrh⟩, ⟨hil, hih⟩⟩ := hz
  simp only [Complex.zero_re, Complex.zero_im] at *
  rcases b.excludesZero_correct.mp h with h | h | h | h
  · have : (0 : ℝ) < (b.reLo : ℝ) := by exact_mod_cast h
    exact (not_le_of_gt this) hrl
  · have : (b.reHi : ℝ) < 0 := by exact_mod_cast h
    exact (not_le_of_gt this) hrh
  · have : (0 : ℝ) < (b.imLo : ℝ) := by exact_mod_cast h
    exact (not_le_of_gt this) hil
  · have : (b.imHi : ℝ) < 0 := by exact_mod_cast h
    exact (not_le_of_gt this) hih

/-- Every supplied rectangle encloses the corresponding exact value. This is a
proof obligation for an analytic backend, not a Boolean supplied by the caller. -/
def Encloses : List Box → (ℕ → ℂ) → Prop
  | [], _ => True
  | b :: bs, a => b.Contains (a 0) ∧ Encloses bs (fun k => a (k + 1))

theorem Witness.sound {bs : List Box} {n : ℕ} (h : Witness bs n)
    (a : ℕ → ℂ) (ha : Encloses bs a) :
    (∀ k < n, a k = 0) ∧ a n ≠ 0 := by
  induction h generalizing a with
  | here hv hn =>
    exact ⟨by intro k hk; omega, Box.excludesZero_sound hn ha.1⟩
  | @next b bs n hv hz hw ih =>
    obtain ⟨hbefore, hne⟩ := ih (fun k => a (k + 1)) ha.2
    refine ⟨?_, hne⟩
    intro k hk
    cases k with
    | zero => exact Box.isZero_sound hz ha.1
    | succ k => exact hbefore k (by omega)

/-- Main semantic theorem: the executable search computes the actual analytic
order, assuming analyticity and proved enclosures of the true derivatives. -/
theorem scan_analyticOrderAt {f : ℂ → ℂ} {center : ℂ} {bs : List Box} {n : ℕ}
    (hf : AnalyticAt ℂ f center)
    (hencl : Encloses bs (fun k => iteratedDeriv k f center))
    (hscan : scan bs = some n) : analyticOrderAt f center = n := by
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mpr
  exact (scan_correct bs n hscan).sound _ hencl

/-- A finite rank and a kernel-checked theorem about the specified function and
center. Both are tied to the exact input boxes by the computation equation. -/
structure AnalyticCertificate (f : ℂ → ℂ) (center : ℂ) (bs : List Box) where
  rank : ℕ
  computed : scan bs = some rank
  correct : analyticOrderAt f center = rank

/-- This function cannot be called for an L-function without a proof that the
boxes enclose its actual derivatives. Proof arguments erase at runtime. -/
def computeRank (f : ℂ → ℂ) (center : ℂ) (bs : List Box)
    (hf : AnalyticAt ℂ f center)
    (hencl : Encloses bs (fun k => iteratedDeriv k f center)) :
    Option (AnalyticCertificate f center bs) :=
  match h : scan bs with
  | none => none
  | some n => some ⟨n, h, scan_analyticOrderAt hf hencl h⟩

theorem computeRank_correct {f : ℂ → ℂ} {center : ℂ} {bs : List Box}
    {hf : AnalyticAt ℂ f center}
    {hencl : Encloses bs (fun k => iteratedDeriv k f center)}
    {c : AnalyticCertificate f center bs}
    (_h : computeRank f center bs hf hencl = some c) :
    scan bs = some c.rank ∧ analyticOrderAt f center = c.rank :=
  ⟨c.computed, c.correct⟩

end VerifiedLcalc
