module

public import VerifiedLcalc.EllipticCurve.MinimalArithmetic
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The integral semistable criterion supplies a unit invariant in every local
coefficient ring. This is a proved Bezout argument, not a modularity field. -/
theorem unit_invariants_of_coprime (e : (WeierstrassCurve ℤ))
    (hs : Int.gcd (e.Δ) e.c₄ = 1)
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsUnit (WeierstrassCurve.baseChange e R).Δ ∨ IsUnit (WeierstrassCurve.baseChange e R).c₄ := by
  have h := (Int.isCoprime_iff_gcd_eq_one.mpr hs).map (Int.castRingHom R)
  rcases h with ⟨a, b, hab⟩
  have hr : a * (WeierstrassCurve.baseChange e R).Δ + b * (WeierstrassCurve.baseChange e R).c₄ = 1 := by
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, WeierstrassCurve.map_c₄, eq_intCast, Int.coe_castRingHom] using hab
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one hr).imp
    (fun h => isUnit_of_mul_isUnit_right h) (fun h => isUnit_of_mul_isUnit_right h)

/-- Semistable input equations are minimal at every finite place. -/
theorem semistable_isMinimal (e : (WeierstrassCurve ℤ))
    (hs : Int.gcd (e.Δ) e.c₄ = 1)
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
    WeierstrassCurve.IsMinimal R ((WeierstrassCurve.baseChange e R).baseChange K) :=
  WeierstrassCurve.isMinimal_of_unit_invariants _ (unit_invariants_of_coprime e hs R)

/-- The supplied integer equation gives every local Euler polynomial for a
semistable curve, including split and nonsplit multiplicative bad primes. -/
theorem semistable_localPolynomial (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0)
    (hs : Int.gcd (e.Δ) e.c₄ = 1)
    (p : ℕ) [Fact p.Prime] :
    ((WeierstrassCurve.baseChange e ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPlace p).adicCompletionIntegers ℚ) =
      1 - Polynomial.C (computeFrobeniusTrace e p) * Polynomial.X +
        Polynomial.C (if goodReduction e p then (p : ℤ) else 0) * Polynomial.X ^ 2 :=
  minimal_localPolynomial e hn p (semistable_isMinimal e hs)

/-- Full prime-power identification, proved uniformly for semistable models. -/
theorem semistable_primePower (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0)
    (hs : Int.gcd (e.Δ) e.c₄ = 1)
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ j) =
      computePrimePowerCoefficient e p j := by
  let : Fact p.Prime := ⟨hp⟩
  rw [LFunction_apply_prime_pow]
  exact localPowerSeries_coeff_eq _ _ _ (semistable_localPolynomial e hn hs p) j

/-- The executable coefficient table is the actual curve coefficient prefix,
with no trace-size restriction or modularity assumption. -/
theorem semistable_prefix (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0)
    (hs : Int.gcd (e.Δ) e.c₄ = 1) (limit : ℕ) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j + 1)) :=
  modelCoefficients_eq_curve e (semistable_primePower e hn hs) limit

end VerifiedLcalc.EllipticCurve
