/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Scan
public import VerifiedLcalc.Certificate.Analytic.EnclosurePredicates

import Mathlib.Data.Rat.Cast.Order

import Mathlib.Tactic

/-! Exact coordinate-rectangle semantics for analytic derivative enclosures. -/

@[expose] public section

namespace VerifiedLcalc

/-- A singleton-zero rectangle can contain only the complex number zero. -/
theorem Box.isZero_sound {b : Box} {z : ℂ}
    (h : b.isZero = true) (hz : b.Contains z) : z = 0 := by
  obtain ⟨hrl, hrh, hil, hih⟩ := b.isZero_correct.mp h
  simp only [Contains, hrl, hrh, hil, hih, Rat.cast_zero,
    Set.Icc_self, Set.mem_singleton_iff] at hz
  exact Complex.ext hz.1 hz.2

/-- A rectangle whose real or imaginary interval excludes zero cannot contain
the complex number zero. -/
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

/-- A finite box witness proves exact vanishing before its index and
nonvanishing at that index for every sequence enclosed by the boxes. -/
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

end VerifiedLcalc
