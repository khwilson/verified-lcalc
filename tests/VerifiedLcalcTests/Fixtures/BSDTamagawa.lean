/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import VerifiedLcalc.EllipticCurve.Tate.Tamagawa

/-! # The intrinsic Tamagawa product of 37.a1

The model has discriminant 37. Its completed local factor is one at the single
multiplicative place of index one and at all places of good reduction.
-/

@[expose] public section

namespace Curve37a1Tamagawa

open VerifiedLcalc VerifiedLcalc.EllipticCurve WeierstrassCurve
open IsDedekindDomain WithZero
open scoped WithZero

/-- The integral equation of 37.a1. -/
def model : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

instance : (model.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

set_option backward.isDefEq.respectTransparency.types false in
private theorem valuation_eq (v : HeightOneSpectrum ℤ) (p k : ℕ) (n : ℤ)
    (hp : v.asIdeal = Ideal.span {(p : ℤ)}) (h : (p : ℤ) ^ k ∣ n)
    (hnext : ¬ (p : ℤ) ^ (k + 1) ∣ n) :
    Valued.v (n : v.adicCompletion ℚ) = exp (-(k : ℤ)) := by
  have hpow (j : ℕ) : v.intValuation n ≤ exp (-(j : ℤ)) ↔ (p : ℤ) ^ j ∣ n := by
    rw [v.intValuation_le_pow_iff_mem, hp, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hlo : exp (-((k + 1 : ℕ) : ℤ)) < v.intValuation n :=
    lt_of_not_ge fun ht => hnext ((hpow (k + 1)).mp ht)
  have hhi := (hpow k).mpr h
  have hne : v.intValuation n ≠ 0 := by
    intro hz
    rw [hz] at hlo
    exact not_lt_zero hlo
  have hv : Valued.v (n : v.adicCompletion ℚ) = v.intValuation n := by
    have he := v.valuedAdicCompletion_eq_valuation' (K := ℚ) (n : ℚ)
    have hf := v.valuation_of_algebraMap (K := ℚ) n
    change v.valuation ℚ (algebraMap ℤ ℚ n) = _ at hf
    have hi : algebraMap ℤ ℚ n = (n : ℚ) := by
      rw [algebraMap_int_eq]
      rfl
    rw [hi] at hf
    have hc := congrFun (v.algebraMap_adicCompletion (K := ℚ) (S := ℚ)) (n : ℚ)
    simp only [Function.comp_apply, Algebra.algebraMap_self_apply] at hc
    have hcast (f : ℚ →+* v.adicCompletion ℚ) : f (n : ℚ) = (n : v.adicCompletion ℚ) :=
      map_intCast f n
    rw [hcast] at hc
    exact (congrArg (fun x : v.adicCompletion ℚ => Valued.v x) hc).trans (he.trans hf)
  rw [hv, ← exp_log hne]
  rw [← exp_log hne] at hlo hhi
  have hlow := exp_lt_exp.mp hlo
  have hhigh := exp_le_exp.mp hhi
  congr 1
  omega

private theorem all_local_factors_one (v : HeightOneSpectrum ℤ) :
    (model.baseChange ℚ).tamagawaNumberAt v = 1 := by
  let p := v.asIdeal.absNorm
  have hprime : p.Prime := (Int.prime_absNorm v.asIdeal).mpr
    ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime)
  have hp : v.asIdeal = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
  by_cases heq : p = 37
  · rw [heq] at hp
    apply tamagawaNumberAt_eq_one_of_valuation_I_one model v
    · exact valuation_eq v 37 1 model.Δ hp (by decide +kernel) (by decide +kernel)
    · simpa using valuation_eq v 37 0 model.c₄ hp (by decide +kernel) (by decide +kernel)
  · apply tamagawaNumberAt_eq_one_of_unit_discriminant model v
    have h : ¬ (p : ℤ) ∣ model.Δ := by
      change ¬ (p : ℤ) ∣ 37
      intro hd
      exact heq ((Nat.prime_dvd_prime_iff_eq hprime (by decide : Nat.Prime 37)).mp
        (by exact_mod_cast hd))
    simpa using valuation_eq v p 0 model.Δ hp (by simp) (by simpa using h)

/-- Every completed local factor equals one, so the intrinsic product is one. -/
theorem product_eq_one : (model.baseChange ℚ).tamagawaProduct (R := ℤ) = 1 := by
  rw [WeierstrassCurve.tamagawaProduct_eq_prod _ ∅ (fun v _ => all_local_factors_one v)]
  simp

/-- The explicit proof attached to the raw Tamagawa product report. -/
def product : TamagawaProductFact model := ⟨1, product_eq_one⟩

certify_ec TamagawaCertificate from
  { equation := model, tamagawaProduct := some 1 }
  with_proofs { tamagawaProduct := some product }

end Curve37a1Tamagawa
