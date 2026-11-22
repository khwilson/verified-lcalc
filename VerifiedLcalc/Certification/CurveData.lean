module

public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic
public import VerifiedLcalc.Certificate.EllipticWitness
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Chord
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral

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

/-- The two candidate integral y-coordinates over x, counted once when they coincide. -/
def integralYFiber (W : WeierstrassCurve ℤ) (x y₀ : ℤ) : Finset ℤ :=
  {y₀, W.toAffine.negY x y₀}

/-- A single checked root determines the full integer fiber over its x-coordinate. -/
theorem mem_integralYFiber_iff {W : WeierstrassCurve ℤ} {x y₀ : ℤ}
    (h₀ : W.toAffine.Equation x y₀) (y : ℤ) :
    y ∈ integralYFiber W x y₀ ↔ W.toAffine.Equation x y := by
  simp only [integralYFiber, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact h₀
    · exact (WeierstrassCurve.Affine.equation_neg (W' := W.toAffine) x y₀).mpr h₀
  · intro hy
    have hprod : (y - y₀) * (y - W.toAffine.negY x y₀) = 0 := by
      simpa only [sub_self, zero_mul] using
        WeierstrassCurve.Affine.Y_sub_Y_mul_Y_sub_negY_eq hy h₀
    simpa only [sub_eq_zero] using mul_eq_zero.mp hprod

end EllipticWitness
end VerifiedLcalc
