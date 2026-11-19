module

public import VerifiedLcalc.EllipticCurve.CentralCore
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- A shifted square times a geometric sequence admits an explicit geometric
majorant. This is deliberately a loose bound, avoiding any heuristic tail. -/
theorem square_geometric_majorant (q : ℝ) (limit k : Nat) (hq : 0 ≤ q) :
    ((k + limit + 1 : Nat) : ℝ) ^ 2 * q ^ (k + limit + 1) ≤
      (((limit + 1 : Nat) : ℝ) ^ 2 * q ^ (limit + 1)) *
        (q * (((limit + 2 : Nat) : ℝ) / (limit + 1 : Nat)) ^ 2) ^ k := by
  let c : ℝ := ((limit + 2 : Nat) : ℝ) / (limit + 1 : Nat)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  induction k with
  | zero => simp
  | succ k ih =>
    have hm : (0 : ℝ) < ((limit + 1 : Nat) : ℝ) := by positivity
    have hstep : ((k + limit + 1 : Nat) : ℝ) + 1 ≤
        c * ((k + limit + 1 : Nat) : ℝ) := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hm).mpr
      push_cast
      nlinarith
    have hsq : (((k + limit + 1 : Nat) : ℝ) + 1) ^ 2 ≤
        c ^ 2 * ((k + limit + 1 : Nat) : ℝ) ^ 2 := by
      simpa [mul_pow] using
        (sq_le_sq₀ (by positivity) (mul_nonneg hc (by positivity))).mpr hstep
    have h1 := mul_le_mul_of_nonneg_right hsq (mul_nonneg (pow_nonneg hq (k + limit + 1)) hq)
    have h2 := mul_le_mul_of_nonneg_right ih (mul_nonneg hq (sq_nonneg c))
    have he : (k + 1 + limit + 1 : Nat) = (k + limit + 1) + 1 := by omega
    calc
      _ ≤ c ^ 2 * ((k + limit + 1 : Nat) : ℝ) ^ 2 *
          (q ^ (k + limit + 1) * q) := by
        simpa only [he, Nat.cast_add, Nat.cast_one, pow_succ q] using h1
      _ = (((k + limit + 1 : Nat) : ℝ) ^ 2 * q ^ (k + limit + 1)) *
          (q * c ^ 2) := by dsimp [c]; ring
      _ ≤ (((limit + 1 : Nat) : ℝ) ^ 2 * q ^ (limit + 1)) *
          (q * c ^ 2) ^ k * (q * c ^ 2) := h2
      _ = _ := by dsimp [c]; rw [pow_succ]; ring


/-- From an actual summation identity and a global coefficient majorant, derive
the truncation error. No database answer or numerical zero assumption is used. -/
theorem central_tail_error (f : Nat → ℝ) (value C q : ℝ) (limit : Nat)
    (hf : HasSum f value) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hr : q * (((limit + 2 : Nat) : ℝ) / (limit + 1 : Nat)) ^ 2 < 1)
    (hb : ∀ j, |f j| ≤ C * (((j + 1 : Nat) : ℝ) ^ 2 * q ^ (j + 1))) :
    |value - ∑ j ∈ Finset.range limit, f j| ≤
      C * ((((limit + 1 : Nat) : ℝ) ^ 2 * q ^ (limit + 1)) /
        (1 - q * (((limit + 2 : Nat) : ℝ) / (limit + 1 : Nat)) ^ 2)) := by
  let ratio := q * (((limit + 2 : Nat) : ℝ) / (limit + 1 : Nat)) ^ 2
  let first := ((limit + 1 : Nat) : ℝ) ^ 2 * q ^ (limit + 1)
  have hratio : 0 ≤ ratio := mul_nonneg hq (sq_nonneg _)
  have hg := (hasSum_geometric_of_lt_one hratio hr).mul_left (C * first)
  have ht := (hasSum_nat_add_iff' limit).mpr hf
  have he := ht.norm_le_of_bounded hg (by
    intro j
    rw [Real.norm_eq_abs]
    exact (hb (j + limit)).trans (by
      have hm := mul_le_mul_of_nonneg_left (square_geometric_majorant q limit j hq) hC
      simpa only [first, ratio, mul_assoc] using hm))
  simpa [Real.norm_eq_abs, ratio, first, div_eq_mul_inv, mul_assoc] using he

end VerifiedLcalc.EllipticCurve
