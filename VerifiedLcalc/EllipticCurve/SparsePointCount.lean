/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Verification.CurveData
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound

/-! # Point counts from a single certified point order and Hasse's bound -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Check that the proposed count is a multiple of the point order and that both adjacent
multiples lie strictly outside the Hasse interval. -/
def isolatesHasseCount (q order : ℕ) (count : ℤ) : Bool :=
  let center : ℤ := q + 1
  let lower := count - (order : ℤ)
  let upper := count + (order : ℤ)
  decide ((order : ℤ) ∣ count ∧ lower < center ∧ center < upper ∧
    4 * (q : ℤ) < (lower - center) ^ 2 ∧ 4 * (q : ℤ) < (upper - center) ^ 2)

private theorem isolatesHasseCount_sound (q order : ℕ) (count actual : ℤ)
    (h : isolatesHasseCount q order count = true)
    (hdiv : (order : ℤ) ∣ actual)
    (hbound : (actual - ((q : ℤ) + 1)) ^ 2 ≤ 4 * (q : ℤ)) : actual = count := by
  have h' := of_decide_eq_true h
  obtain ⟨hcount, hlo, hhi, hl, hu⟩ := h'
  rcases lt_trichotomy actual count with hlt | heq | hgt
  · have hd := Int.le_of_dvd (sub_pos.mpr hlt) (dvd_sub hcount hdiv)
    have hc : (count - (order : ℤ) - ((q : ℤ) + 1)) ^ 2 ≤
        (actual - ((q : ℤ) + 1)) ^ 2 := by
      rw [sub_sq_comm (count - (order : ℤ)), sub_sq_comm actual]
      gcongr
      omega
    exact (not_lt_of_ge (hc.trans hbound) hl).elim
  · exact heq
  · have hd := Int.le_of_dvd (sub_pos.mpr hgt) (dvd_sub hdiv hcount)
    have hc : (count + (order : ℤ) - ((q : ℤ) + 1)) ^ 2 ≤
        (actual - ((q : ℤ) + 1)) ^ 2 := by
      gcongr
      omega
    exact (not_lt_of_ge (hc.trans hbound) hu).elim

/-- A checked order of a point on a good reduction identifies the exact Frobenius trace. -/
theorem frobeniusTrace_of_point_order {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (P : W.toAffine.Point) (order : ℕ) (a : ℤ)
    (horder : addOrderOf P = order)
    (hcount : isolatesHasseCount p order ((p : ℤ) + 1 - a) = true) :
    W.frobeniusTrace = a := by
  have hdiv : order ∣ Nat.card W.toAffine.Point := by
    rw [← horder]
    exact addOrderOf_dvd_natCard P
  have hb := W.hasse_bound
  rw [Nat.card_zmod] at hb
  have hc := isolatesHasseCount_sound p order _ _ hcount (Int.natCast_dvd_natCast.mpr hdiv) hb
  rw [WeierstrassCurve.frobeniusTrace_eq_card_point, Nat.card_zmod, hc]
  omega

/-- Verify an integer coefficient using a supplied point on its finite reduction.
Strip prime factors from the proposed count whenever the smaller multiple annihilates
the point, then check its exact order and isolate the count in the Hasse interval. -/
def pointOrderTraceCheck (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (x y : ℕ) (a : ℤ) : Bool :=
  let W := e.baseChange (ZMod p)
  if hg : goodReduction e p = true then
    letI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr ((goodReduction_correct e p).mp hg)⟩
    let x' : ZMod p := x
    let y' : ZMod p := y
    if h : y' ^ 2 + W.a₁ * x' * y' + W.a₃ * y' =
        x' ^ 3 + W.a₂ * x' ^ 2 + W.a₄ * x' + W.a₆ then
      let P : W.toAffine.Point := .mk (x := x') (y := y') (by
        rwa [WeierstrassCurve.Affine.equation_iff])
      let count : ℤ := (p : ℤ) + 1 - a
      let n := count.toNat
      let order := n.primeFactorsList.foldl (fun d q => if (d / q) • P = 0 then d / q else d) n
      EllipticWitness.exactOrderCheck P order && isolatesHasseCount p order count
    else false
  else false

/-- The point-order verifier proves the actual curve coefficient without modularity.
The supported good reduction supplies the necessary local minimality. -/
theorem pointOrderTraceCheck_sound (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (x y : ℕ) (a : ℤ) (hn : e.Δ ≠ 0) (h : pointOrderTraceCheck e p x y a = true) :
    (e.baseChange ℚ).LFunction p = a := by
  unfold pointOrderTraceCheck at h
  dsimp only at h
  split at h
  · rename_i hg
    let : (e.baseChange (ZMod p)).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr ((goodReduction_correct e p).mp hg)⟩
    split at h
    · obtain ⟨ho, hc⟩ := Bool.and_eq_true_iff.mp h
      have ht := frobeniusTrace_of_point_order _ _ _ a
        (EllipticWitness.exactOrderCheck_sound ho) hc
      have hd : ¬ (p : ℤ) ∣ e.Δ := by
        intro hdiv
        exact (of_decide_eq_true hg) (Int.dvd_iff_emod_eq_zero.mp hdiv)
      have hm := minimal_at_of_discriminant_not_dvd e p
        (fun hdiv => hd (dvd_trans (dvd_pow_self _ (by decide : 12 ≠ 0)) hdiv))
      have he := localPowerSeries_coeff_eq _ _ _ (minimal_localPolynomial e hn p hm) 1
      rw [← pow_one p, LFunction_apply_prime_pow]
      have ha := (computeFrobeniusTrace_correct e p).trans ht
      simpa [computePrimePowerCoefficient, localCoefficient, localPair, ha] using he
    · contradiction
  · contradiction

end VerifiedLcalc.EllipticCurve
