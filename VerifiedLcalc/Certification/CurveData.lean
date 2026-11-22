module

public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic
public import VerifiedLcalc.Certificate.EllipticWitness
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact certificates for stored elliptic-curve arithmetic data

Prime coefficients are checked against the existing finite-field trace evaluator,
with a sufficient local minimality check at every supplied prime. Soundness gives
the actual curve's `LFunction p`, including bad primes, without modularity.
Coordinate certificates establish membership on the supplied integral equation
or its rational base change.
-/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve

namespace EllipticWitness

/-- Each supplied coefficient has a prime index, a certified locally minimal
model, and the claimed exact trace. This is a sufficient, not complete, checker. -/
def primeCoefficientsValid (w : EllipticWitness) : Bool :=
  (w.primeCoefficients.getD []).all fun (p, a) =>
    isPrime p && modelMinimalAt w.equation p &&
      decide (computeFrobeniusTrace w.equation p = a)

/-- Check the explicit Weierstrass equation at each supplied affine pair. -/
def affineCoordinatesValid {R : Type*} [CommRing R] [DecidableEq R]
    (W : WeierstrassCurve R) (points : List (R × R)) : Bool :=
  -- Polynomial evaluation in the specification is noncomputable.
  points.all fun (x, y) =>
    decide (y ^ 2 + W.a₁ * x * y + W.a₃ * y =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

/-- Passing the finite check proves Mathlib's affine equation for every listed pair. -/
theorem affineCoordinatesValid_sound {R : Type*} [CommRing R] [DecidableEq R]
    (W : WeierstrassCurve R) (points : List (R × R))
    (h : affineCoordinatesValid W points = true) (x y : R)
    (hxy : (x, y) ∈ points) : W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  exact of_decide_eq_true (List.all_eq_true.mp h (x, y) hxy)

/-- Check precisely the supplied integer solutions, without searching for others. -/
def integralCoordinatesValid (w : EllipticWitness) : Bool :=
  affineCoordinatesValid w.equation (w.integralCoordinates.getD [])

/-- Check annihilation and the proper multiples obtained from prime divisors of the claim.
The bound limits work for untrusted input. -/
def exactOrderCheck {A : Type*} [AddMonoid A] [DecidableEq A] (P : A) (n : Nat) : Bool :=
  decide (0 < n ∧ n ≤ 256) && decide (n • P = 0) &&
    (List.range (n + 1)).all fun p =>
      if isPrime p && decide (p ∣ n) then decide ((n / p) • P ≠ 0) else true

/-- A checked claim is the additive order in the supplied group. -/
theorem exactOrderCheck_sound {A : Type*} [AddMonoid A] [DecidableEq A] {P : A} {n : Nat}
    (h : exactOrderCheck P n = true) : addOrderOf P = n := by
  obtain ⟨hbound, hdiv⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hn, hzero⟩ := Bool.and_eq_true_iff.mp hbound
  have hpos := (of_decide_eq_true hn).1
  apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul (of_decide_eq_true hzero)
  intro p hp hpn
  have hmem : p ∈ List.range (n + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn))
  have hpcheck : (isPrime p && decide (p ∣ n)) = true :=
    Bool.and_eq_true_iff.mpr ⟨(isPrime_correct p).mpr hp, decide_eq_true hpn⟩
  exact of_decide_eq_true (by simpa only [hpcheck, if_true] using List.all_eq_true.mp hdiv p hmem)

/-- A successful finite check proves every listed value is the actual prime
coefficient of the rational curve, with local minimality handled at bad primes. -/
theorem primeCoefficientsValid_sound (w : EllipticWitness) (hn : w.equation.Δ ≠ 0)
    (h : w.primeCoefficientsValid = true) (p : Nat) (a : Int)
    (ha : (p, a) ∈ w.primeCoefficients.getD []) :
    (w.equation.baseChange ℚ).LFunction p = a := by
  have hc := List.all_eq_true.mp h (p, a) ha
  obtain ⟨hchecks, ht⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hp, hm⟩ := Bool.and_eq_true_iff.mp hchecks
  let : Fact p.Prime := ⟨(isPrime_correct p).mp hp⟩
  have hm' := modelMinimalAt_correct w.equation p hm
  have he := localPowerSeries_coeff_eq _ _ _
    (minimal_localPolynomial w.equation hn p hm') 1
  rw [← pow_one p, LFunction_apply_prime_pow]
  simpa [computePrimePowerCoefficient, localCoefficient, localPair,
    of_decide_eq_true ht] using he

/-- A successful coordinate check proves every supplied pair satisfies the
existing Mathlib affine Weierstrass equation over the integers. -/
theorem integralCoordinatesValid_sound (w : EllipticWitness)
    (h : w.integralCoordinatesValid = true) (x y : Int)
    (hxy : (x, y) ∈ w.integralCoordinates.getD []) : w.equation.toAffine.Equation x y :=
  affineCoordinatesValid_sound _ _ h x y hxy

end EllipticWitness
end VerifiedLcalc
