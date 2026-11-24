/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module
public import VerifiedLcalc.Numerics.RealInterval
public import VerifiedLcalc.Numerics.PolynomialTail
public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Fourier truncation and certified pointwise interval bounds for quadrature -/

@[expose] public section
namespace VerifiedLcalc.Numerics
open MeasureTheory Set

private theorem polynomial_range (a : Nat → Int) (q : ℝ) (M k : Nat) :
    polynomialValue q ((List.range M).map (fun j => a (j+k))) =
      ∑ j ∈ Finset.range M, (a (j+k) : ℝ)*q^j := by
  induction M generalizing k with
  | zero => simp [polynomialValue]
  | succ M ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, polynomialValue]
    have he : (fun x => a (x+1+k)) = (fun x => a (x+(k+1))) := by funext x; congr 1; omega
    simp only [Function.comp_def, he]
    rw [ih, Finset.sum_range_succ']
    simp only [zero_add, pow_zero, mul_one]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    have he' : j+(k+1) = j+1+k := by omega
    rw [he']
    ring

/-- A Fourier prefix is the Horner polynomial multiplied by its first power of the argument. -/
theorem prefix_polynomial (a : Nat → Int) (q : ℝ) (M : Nat) :
    (∑ j ∈ Finset.range M, (a (j+1) : ℝ)*q^(j+1)) =
      q*polynomialValue q ((List.range M).map (fun j => a (j+1))) := by
  rw [polynomial_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- Pointwise truncation of the actual Fourier series, using a proved cubic
coefficient bound and an outward upper bound on exp(-alpha*t). -/
theorem fourier_prefix_error (a : Nat → Int) (cs : List Int) (q Q value : ℝ) (rem : Rat)
    (hc : cs = (List.range cs.length).map (fun j => a (j+1)))
    (hf : HasSum (fun j => (a (j+1) : ℝ)*q^(j+1)) value)
    (hb : ∀ j, |(a (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3)
    (hq : 0 ≤ q) (hQ : q ≤ Q) (Qrat : Rat) (heQ : Q = (Qrat : ℝ))
    (hr : polynomialTailBound Qrat 3 cs.length = some rem) :
    |value-q*polynomialValue q cs| ≤ (rem : ℝ) := by
  obtain ⟨hQr, hratio, hrem⟩ := polynomialTailBound_correct hr
  have hQr' : (0 : ℝ) ≤ Q := hq.trans hQ
  have hratio' : Q*(((cs.length+2 : Nat) : ℝ)/(cs.length+1 : Nat))^3 < 1 := by
    rw [heQ]
    unfold polynomialTailRatio at hratio
    have hcast : ((Qrat*((cs.length+2 : Rat)/(cs.length+1 : Rat))^3 : Rat) : ℝ) < 1 := by
      exact_mod_cast hratio
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_one,
      Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hcast
  have h := polynomial_tail_error (fun j => (a (j+1) : ℝ)*q^(j+1)) value 1 Q 3 cs.length hf
    (by norm_num) hQr' hratio' (by
      intro j
      rw [abs_mul, abs_of_nonneg (pow_nonneg hq _)]
      simpa using mul_le_mul (hb j) (pow_le_pow_left₀ hq hQ _) (pow_nonneg hq _) (by positivity))
  rw [prefix_polynomial] at h
  have hrem' : (rem : ℝ) = ((cs.length+1 : Nat) : ℝ)^3*Q^(cs.length+1)/
      (1-Q*(((cs.length+2 : Nat) : ℝ)/(cs.length+1 : Nat))^3) := by
    rw [hrem, heQ]
    push_cast [polynomialTailRatio]
    rfl
  simp only [← hc] at h
  simpa only [one_mul, ← hrem'] using h

open Inclusion.IntervalDyadicReal in
private theorem dyadicPolynomialBounds_exp_toRat (lo hi : Rat) (bits : Nat)
    (cs : List Int) :
    Prod.map _root_.Dyadic.toRat _root_.Dyadic.toRat
        (dyadicPolynomialBounds bits (rationalExpDyadicBounds lo hi bits) cs) =
      polynomialBounds bits (rationalExpBounds lo hi bits) cs := by
  apply dyadicPolynomialBounds_toRat
  change 0 ≤ (expBounds (lo.toDyadic bits) bits).1
  apply _root_.Dyadic.toRat_le_toRat_iff.mp
  change (0 : Rat) ≤ (expBounds (lo.toDyadic bits) bits).1.toRat
  cases lo.toDyadic bits with
  | zero =>
    change (0 : Rat) ≤ (1 : _root_.Dyadic).toRat
    decide
  | ofOdd num exponent h =>
    simp only [expBounds, expOfNatWithPrec_eq, _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
    positivity

/-- Integral bounds of a cell follow from genuine pointwise bounds of log and
the Fourier series. The partial series is evaluated by rounded Horner arithmetic. -/
theorem derivativeCellBounds_sound (a : Nat → Int) (cs : List Int)
    (al ah left right : Rat) (bits : Nat) (cell : RealInterval)
    (alpha : ℝ) (f : ℝ → ℝ)
    (hl : 1 ≤ left) (hlr : left ≤ right)
    (ha : (al : ℝ) ≤ alpha ∧ alpha ≤ (ah : ℝ)) (ha0 : 0 < alpha)
    (hc : cs = (List.range cs.length).map (fun j => a (j+1)))
    (hb : ∀ j, |(a (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3)
    (hf : ∀ t, 0 < t → HasSum (fun j => (a (j+1) : ℝ)*Real.exp (-alpha*t)^(j+1)) (f t))
    (hi : IntervalIntegrable (fun t => Real.log t*f t) volume (left : ℝ) (right : ℝ))
    (he : EllipticCurve.derivativeCellBounds cs al ah left right bits = some cell) :
    cell.Contains (∫ t in (left : ℝ)..(right : ℝ), Real.log t*f t) := by
  unfold EllipticCurve.derivativeCellBounds at he
  dsimp only at he
  have hq : Prod.map Dyadic.toRat Dyadic.toRat (rationalExpDyadicBounds (-ah * right)
      (-al * left) bits) = rationalExpBounds (-ah * right) (-al * left) bits := rfl
  rw [dyadicPolynomialBounds_exp_toRat, hq] at he
  cases hr : polynomialTailBound (rationalExpBounds (-ah*right) (-al*left) bits).2 3 cs.length with
  | none =>
    rw [hr] at he
    contradiction
  | some rem =>
    rw [hr] at he
    replace he := Option.some.inj he
    subst cell
    apply roundInterval_sound
    have hp (t : ℝ) (ht : t ∈ Icc (left : ℝ) (right : ℝ)) :
        (intervalMul
          ((logBounds left 8 bits).1,(logBounds right 8 bits).2)
          ((intervalMul (rationalExpBounds (-ah*right) (-al*left) bits)
            (polynomialBounds bits (rationalExpBounds (-ah*right) (-al*left) bits) cs)).1-rem,
           (intervalMul (rationalExpBounds (-ah*right) (-al*left) bits)
            (polynomialBounds bits (rationalExpBounds (-ah*right) (-al*left) bits) cs)).2+rem)).Contains
          (Real.log t*f t) := by
      have hl' : (1 : ℝ) ≤ (left : ℝ) := by exact_mod_cast hl
      have hpos : 0 < t := by linarith [ht.1]
      have hq := rationalExpBounds_correct (-ah*right) (-al*left) bits (-alpha*t)
        (by push_cast; nlinarith [ht.2]) (by push_cast; nlinarith [ht.1])
      have hpol := polynomialBounds_sound bits _ (Real.exp (-alpha*t)) hq cs
      have hprefix := intervalMul_sound _ _ _ _ hq hpol
      have herr := fourier_prefix_error a cs (Real.exp (-alpha*t)) _ (f t) rem hc
        (hf t hpos) hb (Real.exp_nonneg _) hq.2 _ rfl hr
      have hbound : RealInterval.Contains
          ((intervalMul (rationalExpBounds (-ah*right) (-al*left) bits)
            (polynomialBounds bits (rationalExpBounds (-ah*right) (-al*left) bits) cs)).1-rem,
           (intervalMul (rationalExpBounds (-ah*right) (-al*left) bits)
            (polynomialBounds bits (rationalExpBounds (-ah*right) (-al*left) bits) cs)).2+rem) (f t) := by
        change (_ : ℝ) ≤ f t ∧ f t ≤ _
        push_cast
        have he := abs_le.mp herr
        constructor <;> linarith [hprefix.1,hprefix.2,he.1,he.2]
      apply intervalMul_sound _ _ _ _ _ hbound
      exact ⟨(logBounds_sound left 8 bits hl).1.trans (Real.log_le_log (by linarith) ht.1),
        (Real.log_le_log hpos ht.2).trans (logBounds_sound right 8 bits (hl.trans hlr)).2⟩
    let b := intervalMul
      ((logBounds left 8 bits).1,(logBounds right 8 bits).2)
      ((intervalMul (rationalExpBounds (-ah*right) (-al*left) bits)
        (polynomialBounds bits (rationalExpBounds (-ah*right) (-al*left) bits) cs)).1-rem,
       (intervalMul (rationalExpBounds (-ah*right) (-al*left) bits)
        (polynomialBounds bits (rationalExpBounds (-ah*right) (-al*left) bits) cs)).2+rem)
    have hlr' : (left : ℝ) ≤ (right : ℝ) := by exact_mod_cast hlr
    have hlo := intervalIntegral.integral_mono_on hlr' (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (b.1 : ℝ)) volume _ _) hi (fun t ht => (hp t ht).1)
    have hhi := intervalIntegral.integral_mono_on hlr' hi (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (b.2 : ℝ)) volume _ _) (fun t ht => (hp t ht).2)
    change (((intervalMul (right-left,right-left) b).1 : Rat) : ℝ) ≤
      (∫ t in (left : ℝ)..(right : ℝ), Real.log t*f t) ∧
      (∫ t in (left : ℝ)..(right : ℝ), Real.log t*f t) ≤
        (((intervalMul (right-left,right-left) b).2 : Rat) : ℝ)
    simp only [intervalMul, ite_eq_left (sub_nonneg.mpr hlr), ite_self,
      Rat.cast_mul, Rat.cast_sub]
    constructor
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using hlo
    · simpa only [intervalIntegral.integral_const, smul_eq_mul] using hhi
end VerifiedLcalc.Numerics
