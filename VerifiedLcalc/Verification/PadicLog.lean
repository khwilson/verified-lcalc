/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.OrdinaryPadicSigma
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity

/-! # Finite rational evaluation of the ordinary p-adic logarithm -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

variable {p : ℕ} [Fact p.Prime]

private theorem norm_inv_natCast_le (k : ℕ) (hk : 0 < k) :
    ‖((k : ℚ_[p])⁻¹)‖ ≤ (k : ℝ) := by
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hk.ne'),
    Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]
  exact_mod_cast Nat.le_of_dvd hk (pow_multiplicity_dvd p k)

private theorem logTerm_le (z : ℚ_[p]) (hz : ‖z‖ ≤ (p : ℝ)⁻¹) (k : ℕ) :
    ‖padicLogOneAddTerm z k‖ ≤ (p : ℝ)⁻¹ * (2 / p : ℝ) ^ k := by
  rw [padicLogOneAddTerm, div_eq_mul_inv, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_neg, norm_one, one_pow, one_mul]
  have hk : (k + 1 : ℝ) ≤ 2 ^ k := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k)))
  calc
    _ ≤ ((p : ℝ)⁻¹) ^ (k + 1) * (2 : ℝ) ^ k := by
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
        ((norm_inv_natCast_le (k + 1) (by omega)).trans (by simpa using hk))
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ, div_eq_mul_inv, mul_pow]; ring

private theorem logTerm_summable (hp : 2 < p) (z : ℚ_[p])
    (hz : ‖z‖ ≤ (p : ℝ)⁻¹) : Summable (padicLogOneAddTerm z) := by
  have h : 0 ≤ (2 / p : ℝ) ∧ (2 / p : ℝ) < 1 :=
    ⟨by positivity, (div_lt_one (by positivity)).mpr (by exact_mod_cast hp)⟩
  exact ((summable_geometric_of_lt_one h.1 h.2).mul_left ((p : ℝ)⁻¹)).of_norm_bounded
    (logTerm_le z hz)

private theorem norm_pow_sub_pow_le {z w : ℚ_[p]} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (k : ℕ) : ‖z ^ k - w ^ k‖ ≤ ‖z - w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : z ^ (k + 1) - w ^ (k + 1) =
        (z ^ k - w ^ k) * z + w ^ k * (z - w) := by rw [pow_succ, pow_succ]; ring
    rw [he]
    refine (IsUltrametricDist.norm_add_le_max ..).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw)

private theorem rationalPadicLogPrefix_cast (w : ℚ) (N : ℕ) :
    (rationalPadicLogPrefix w N : ℚ_[p]) =
      ∑ k ∈ Finset.range N, padicLogOneAddTerm (w : ℚ_[p]) k := by
  induction N with
  | zero => simp [rationalPadicLogPrefix]
  | succ N ih =>
    unfold rationalPadicLogPrefix at *
    rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add,
      Finset.sum_range_succ, ih]
    simp [padicLogOneAddTerm]

/-- Perturbing the logarithm argument and truncating its series yields the larger of
the finite rounding bound and the geometric tail bound. -/
theorem norm_padicLog_sub_prefix_le (hp : 2 < p) (z : ℚ_[p]) (w : ℚ) (N : ℕ)
    (hz : ‖z‖ ≤ (p : ℝ)⁻¹) (hw : ‖(w : ℚ_[p])‖ ≤ 1) :
    ‖(∑' k, padicLogOneAddTerm z k) - (rationalPadicLogPrefix w N : ℚ_[p])‖ ≤
      max ((N : ℝ) * ‖z - (w : ℚ_[p])‖) ((p : ℝ)⁻¹ * (2 / p : ℝ) ^ N) := by
  rw [rationalPadicLogPrefix_cast]
  let f := padicLogOneAddTerm z
  let g := padicLogOneAddTerm (w : ℚ_[p])
  rw [← (logTerm_summable hp z hz).sum_add_tsum_nat_add N]
  change ‖(∑ k ∈ Finset.range N, f k) + (∑' i, f (i + N)) -
    ∑ k ∈ Finset.range N, g k‖ ≤ _
  rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
  refine (IsUltrametricDist.norm_add_le_max ..).trans (max_le_max ?_ ?_)
  · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    · positivity
    intro k hk
    have hkN : k + 1 ≤ N := by simpa using Finset.mem_range.mp hk
    have hz' : ‖z‖ ≤ 1 := hz.trans (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))
    have he : f k - g k = (-1 : ℚ_[p]) ^ k *
        (z ^ (k + 1) - (w : ℚ_[p]) ^ (k + 1)) * (((k + 1 : ℕ) : ℚ_[p])⁻¹) := by
      simp only [f, g, padicLogOneAddTerm, div_eq_mul_inv]; ring
    rw [he, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_comm]
    exact mul_le_mul ((norm_inv_natCast_le _ (by omega)).trans (by exact_mod_cast hkN))
      (norm_pow_sub_pow_le hz' hw _) (norm_nonneg _) (by positivity)
  · apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro i
    refine (logTerm_le z hz _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact pow_le_pow_of_le_one (by positivity)
      ((div_le_one (by positivity)).mpr (by exact_mod_cast hp.le)) (by omega)

end VerifiedLcalc.EllipticCurve
