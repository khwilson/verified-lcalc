/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Correctness
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction

/-! # Bounding rational torsion using good reduction

At an odd prime of good reduction, the reduction map is injective on all
rational torsion. The gcd of certified reduced point counts therefore bounds
the order of the actual torsion subgroup.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

open IsDedekindDomain WeierstrassCurve

/-- Every rational prime has sufficiently small ramification at the odd prime
ideal `(p)` for the full torsion reduction theorem. -/
private theorem prime_notMem_span_pow {p q : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (hq : q.Prime) : (q : ℤ) ∉ (Ideal.span {(p : ℤ)}) ^ (q - 1) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← Nat.cast_pow,
    Int.natCast_dvd_natCast]
  intro h
  have hpq : p ∣ q := (dvd_pow_self p (by have := hq.two_le; omega)).trans h
  have hqp := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  subst q
  have hexp : p - 1 ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (by
    simpa only [pow_one] using h)
  have := hp.two_le
  omega

/-- At an odd prime where the supplied integral equation has good reduction,
the full rational torsion order divides the computed finite-field point count. -/
theorem card_torsion_dvd_computePointCount (e : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] (hp₂ : p ≠ 2) (hg : goodReduction e p = true) :
    Nat.card (AddCommGroup.torsion (e.baseChange ℚ).toAffine.Point) ∣
      computePointCount e p := by
  classical
  have hp : p.Prime := Fact.out
  let v := HeightOneSpectrum.ofPrime
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp hp))
  have hv : v.asIdeal = Ideal.span {(p : ℤ)} := rfl
  have hΔ : e.Δ ∉ v.asIdeal := by
    rw [hv, Ideal.mem_span_singleton]
    simpa only [goodReduction, decide_eq_true_eq, Int.dvd_iff_emod_eq_zero] using hg
  let := e.isElliptic_integralModel_baseChange (K := ℚ) v hΔ
  have h := Affine.Point.card_torsion_dvd_card_reduction
    (W := (e.baseChange ℚ).toAffine) v fun q hq => by
      rw [hv]
      exact prime_notMem_span_pow hp hp₂ hq
  rw [e.card_point_reduction_baseChange v p hv] at h
  have hred : (e.baseChange (ZMod p)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr ((goodReduction_correct e p).mp hg)⟩
  rw [computePointCount_correct, WeierstrassCurve.pointCount_eq_card_point]
  exact h

/-- Verify two odd primes of good reduction and the gcd of their exact point counts. -/
def checkTorsionBound (e : WeierstrassCurve ℤ) (p q bound : ℕ) : Bool :=
  isPrime p && (p != 2) && goodReduction e p &&
    isPrime q && (q != 2) && goodReduction e q &&
    (Nat.gcd (computePointCount e p) (computePointCount e q) == bound) && (bound != 0)

/-- A validated gcd is positive and divisible by the rational torsion order. -/
theorem checkTorsionBound_correct (e : WeierstrassCurve ℤ) (p q bound : ℕ)
    (h : checkTorsionBound e p q bound = true) :
    Nat.card (AddCommGroup.torsion (e.baseChange ℚ).toAffine.Point) ∣ bound ∧ 0 < bound := by
  simp only [checkTorsionBound, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    isPrime_correct, and_assoc] at h
  rcases h with ⟨hp, hp₂, hpg, hq, hq₂, hqg, rfl, hpos⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨Nat.dvd_gcd (card_torsion_dvd_computePointCount e p hp₂ hpg)
    (card_torsion_dvd_computePointCount e q hq₂ hqg), Nat.pos_of_ne_zero hpos⟩

/-- A gcd of one certifies exact triviality of the rational torsion subgroup. -/
theorem card_torsion_eq_one_of_checkTorsionBound (e : WeierstrassCurve ℤ) (p q : ℕ)
    (h : checkTorsionBound e p q 1 = true) :
    Nat.card (AddCommGroup.torsion (e.baseChange ℚ).toAffine.Point) = 1 :=
  Nat.dvd_one.mp (checkTorsionBound_correct e p q 1 h).1

end VerifiedLcalc.EllipticCurve
