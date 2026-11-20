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
Integral-coordinate certificates establish membership only, on the supplied
integral equation. They make no completeness or algebraic-rank claim.
-/

namespace VerifiedLcalc
open EllipticCurve

/-- Supplied arithmetic data, independently of any analytic-rank witness.
Prime indices are explicit; integral points are affine integer coordinate pairs. -/
structure CurveDataWitness where
  equation : WeierstrassCurve ℤ
  primeCoefficients : List (Nat × Int) := []
  integralCoordinates : List (Int × Int) := []
  analyticWitness : Option EllipticWitness := none

namespace CurveDataWitness

/-- Existing rank-only inputs are a special case of the common optional-facts record. -/
def ofAnalyticWitness (w : EllipticWitness) : CurveDataWitness :=
  match w with
  | .central r _ _ => { equation := r.equation, analyticWitness := some w }
  | .derivative r _ _ => { equation := r.equation, analyticWitness := some w }

@[simp] theorem ofAnalyticWitness_analyticWitness (w : EllipticWitness) :
    (ofAnalyticWitness w).analyticWitness = some w := by
  cases w <;> rfl

theorem ofAnalyticWitness_equation (w : EllipticWitness) :
    (ofAnalyticWitness w).equation =
      match w with
      | .central r _ _ => r.equation
      | .derivative r _ _ => r.equation := by
  cases w <;> rfl

/-- Each supplied coefficient has a prime index, a certified locally minimal
model, and the claimed exact trace. This is a sufficient, not complete, checker. -/
def primeCoefficientsValid (w : CurveDataWitness) : Bool :=
  w.primeCoefficients.all fun (p, a) =>
    isPrime p && modelMinimalAt w.equation p &&
      decide (computeFrobeniusTrace w.equation p = a)

/-- Check precisely the supplied integer solutions, without searching for others. -/
def integralCoordinatesValid (w : CurveDataWitness) : Bool :=
  -- Polynomial.evalEval is noncomputable; equation_iff supplies this executable reflection.
  w.integralCoordinates.all fun (x, y) =>
    decide (y ^ 2 + w.equation.a₁ * x * y + w.equation.a₃ * y =
      x ^ 3 + w.equation.a₂ * x ^ 2 + w.equation.a₄ * x + w.equation.a₆)

/-- A successful finite check proves every listed value is the actual prime
coefficient of the rational curve, with local minimality handled at bad primes. -/
theorem primeCoefficientsValid_sound (w : CurveDataWitness) (hn : w.equation.Δ ≠ 0)
    (h : w.primeCoefficientsValid = true) (p : Nat) (a : Int)
    (ha : (p, a) ∈ w.primeCoefficients) :
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
theorem integralCoordinatesValid_sound (w : CurveDataWitness)
    (h : w.integralCoordinatesValid = true) (x y : Int)
    (hxy : (x, y) ∈ w.integralCoordinates) : w.equation.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  exact of_decide_eq_true (List.all_eq_true.mp h (x, y) hxy)

end CurveDataWitness
end VerifiedLcalc
