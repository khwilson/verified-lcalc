module
public import VerifiedLcalc.Numerics.RealIntervalCore
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace VerifiedLcalc.Numerics

theorem polynomialTailBound_correct {q : Rat} {power limit : Nat} {tail : Rat}
    (h : polynomialTailBound q power limit = some tail) :
    0 ≤ q ∧ polynomialTailRatio q power limit < 1 ∧
      tail = (limit+1 : Rat)^power*q^(limit+1)/(1-polynomialTailRatio q power limit) := by
  unfold polynomialTailBound at h
  dsimp only at h
  split at h
  · next hc => cases h; exact ⟨hc.1,hc.2,rfl⟩
  · simp at h

theorem polynomial_geometric_majorant (q : ℝ) (power limit k : Nat) (hq : 0 ≤ q) :
    ((k+limit+1 : Nat) : ℝ)^power*q^(k+limit+1) ≤
      ((limit+1 : Nat) : ℝ)^power*q^(limit+1)*
        (q*(((limit+2 : Nat) : ℝ)/(limit+1 : Nat))^power)^k := by
  let c : ℝ := ((limit+2 : Nat) : ℝ)/(limit+1 : Nat)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  induction k with
  | zero => simp
  | succ k ih =>
    have hm : (0 : ℝ) < (limit+1 : Nat) := by positivity
    have hstep : ((k+limit+1 : Nat) : ℝ)+1 ≤ c*(k+limit+1 : Nat) := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hm).mpr
      push_cast
      nlinarith
    have hp : (((k+limit+1 : Nat) : ℝ)+1)^power ≤ c^power*(k+limit+1 : Nat)^power := by
      simpa [mul_pow] using pow_le_pow_left₀ (by positivity) hstep power
    have h1 := mul_le_mul_of_nonneg_right hp (mul_nonneg (pow_nonneg hq (k+limit+1)) hq)
    have h2 := mul_le_mul_of_nonneg_right ih (mul_nonneg hq (pow_nonneg hc power))
    have he : k+1+limit+1 = (k+limit+1)+1 := by omega
    calc
      _ ≤ c^power*(k+limit+1 : Nat)^power*(q^(k+limit+1)*q) := by
        simpa only [he, Nat.cast_add, Nat.cast_one, pow_succ q] using h1
      _ = ((k+limit+1 : Nat) : ℝ)^power*q^(k+limit+1)*(q*c^power) := by ring
      _ ≤ ((limit+1 : Nat) : ℝ)^power*q^(limit+1)*(q*c^power)^k*(q*c^power) := h2
      _ = _ := by dsimp [c]; rw [pow_succ]; ring

theorem polynomial_tail_error (f : Nat → ℝ) (value C q : ℝ) (power limit : Nat)
    (hf : HasSum f value) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hr : q*(((limit+2 : Nat) : ℝ)/(limit+1 : Nat))^power < 1)
    (hb : ∀ j, |f j| ≤ C*((j+1 : Nat) : ℝ)^power*q^(j+1)) :
    |value-∑ j ∈ Finset.range limit, f j| ≤
      C*((limit+1 : Nat) : ℝ)^power*q^(limit+1)/
        (1-q*(((limit+2 : Nat) : ℝ)/(limit+1 : Nat))^power) := by
  let ratio := q*(((limit+2 : Nat) : ℝ)/(limit+1 : Nat))^power
  let first := ((limit+1 : Nat) : ℝ)^power*q^(limit+1)
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hg := (hasSum_geometric_of_lt_one hratio hr).mul_left (C*first)
  have ht := (hasSum_nat_add_iff' limit).mpr hf
  have he := ht.norm_le_of_bounded hg (by
    intro j
    rw [Real.norm_eq_abs]
    exact (hb (j+limit)).trans (by
      have hm := mul_le_mul_of_nonneg_left (polynomial_geometric_majorant q power limit j hq) hC
      simpa only [first, ratio, mul_assoc] using hm))
  simpa [Real.norm_eq_abs, ratio, first, div_eq_mul_inv, mul_assoc] using he
end VerifiedLcalc.Numerics
