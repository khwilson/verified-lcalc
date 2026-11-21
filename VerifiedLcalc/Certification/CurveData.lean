module

public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic
public import VerifiedLcalc.Certificate.EllipticWitness
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral

@[expose] public section

/-!
# Exact certificates for stored elliptic-curve arithmetic data

Prime coefficients are checked against the existing finite-field trace evaluator,
with a sufficient local minimality check at every supplied prime. Soundness gives
the actual curve's `LFunction p`, including bad primes, without modularity.
Coordinate certificates establish membership on the supplied integral equation
or its rational base change.
-/

namespace VerifiedLcalc
open EllipticCurve

namespace EllipticWitness

/-- Each supplied coefficient has a prime index, a certified locally minimal
model, and the claimed exact trace. This is a sufficient, not complete, checker. -/
def primeCoefficientsValid (w : EllipticWitness) : Bool :=
  (w.primeCoefficients.getD []).all fun (p, a) =>
    isPrime p && modelMinimalAt w.equation p &&
      decide (computeFrobeniusTrace w.equation p = a)

/-- Check precisely the supplied integer solutions, without searching for others. -/
def integralCoordinatesValid (w : EllipticWitness) : Bool :=
  -- Polynomial.evalEval is noncomputable; equation_iff supplies this executable reflection.
  (w.integralCoordinates.getD []).all fun (x, y) =>
    decide (y ^ 2 + w.equation.a₁ * x * y + w.equation.a₃ * y =
      x ^ 3 + w.equation.a₂ * x ^ 2 + w.equation.a₄ * x + w.equation.a₆)

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
    (hxy : (x, y) ∈ w.integralCoordinates.getD []) : w.equation.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  exact of_decide_eq_true (List.all_eq_true.mp h (x, y) hxy)

/-- Check a finite list of rational affine coordinate pairs using the explicit equation. -/
def rationalCoordinatesValid (W : WeierstrassCurve ℚ) (points : List (Rat × Rat)) : Bool :=
  points.all fun (x, y) =>
    decide (y ^ 2 + W.a₁ * x * y + W.a₃ * y =
      x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

/-- Valid rational pairs satisfy Mathlib's affine equation on the rational model. -/
theorem rationalCoordinatesValid_sound (W : WeierstrassCurve ℚ) (points : List (Rat × Rat))
    (h : rationalCoordinatesValid W points = true) (x y : Rat)
    (hxy : (x, y) ∈ points) : W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  exact of_decide_eq_true (List.all_eq_true.mp h (x, y) hxy)

end EllipticWitness
end VerifiedLcalc
