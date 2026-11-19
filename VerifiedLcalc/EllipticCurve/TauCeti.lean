module

public import VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount
public import VerifiedLcalc.EllipticCurve.Correctness
public import VerifiedLcalc.EllipticCurve.Euler
public import VerifiedLcalc.EllipticCurve.Bounds
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open WeierstrassCurve

/-- Our enumerator agrees with TauCeti's projective-model count, including at
singular reduction. -/
theorem computePointCount_eq_pointCount (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime] :
    computePointCount e p = (WeierstrassCurve.baseChange e (ZMod p)).pointCount := by
  rw [computePointCount_correct, WeierstrassCurve.pointCount_def]
  rfl

theorem frobeniusTrace_eq_tauceti (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime] :
    frobeniusTrace e p = (WeierstrassCurve.baseChange e (ZMod p)).frobeniusTrace := by
  rw [frobeniusTrace, computePointCount_eq_pointCount, WeierstrassCurve.frobeniusTrace_def]
  simp [Nat.card_eq_fintype_card]

section Local
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [Finite (IsLocalRing.ResidueField R)]

/-- The arithmetic bridge requires an identification with the reduction of a
minimal local model. No arbitrary input model is silently declared minimal. -/
theorem localPolynomial_eq_modelFactor (e : (WeierstrassCurve ℤ)) (p : ℕ)
    [Fact p.Prime] (W : WeierstrassCurve K)
    (k : IsLocalRing.ResidueField R ≃+* ZMod p)
    (hmodel : ((W.minimal R).reduction R).map k.toRingHom = WeierstrassCurve.baseChange e (ZMod p)) :
    W.localPolynomial R =
      1 - Polynomial.C (modelFactor e p).trace * Polynomial.X +
        Polynomial.C (modelFactor e p).quadratic * Polynomial.X ^ 2 := by
  have ht : ((W.minimal R).reduction R).frobeniusTrace = frobeniusTrace e p := by
    rw [frobeniusTrace_eq_tauceti, ← hmodel, WeierstrassCurve.frobeniusTrace_map_equiv]
  have hc : Nat.card (IsLocalRing.ResidueField R) = p := by
    rw [Nat.card_congr k.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hg : (W.minimal R).HasGoodReduction R ↔ goodReduction e p = true := by
    rw [WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction,
      WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, goodReduction_correct,
      ← hmodel, WeierstrassCurve.map_Δ]
    constructor
    · intro hn hz
      exact hn (k.injective (by simpa using hz))
    · intro hn hz
      apply hn
      simp [hz]
  by_cases hgood : goodReduction e p = true
  · rw [W.localPolynomial_eq_of_hasGoodReduction R (hg.mpr hgood), ht, hc]
    simp [modelFactor, hgood]
  · rw [W.localPolynomial_eq_of_not_hasGoodReduction R (mt hg.mp hgood), ht]
    simp [modelFactor, hgood]

omit [Finite (IsLocalRing.ResidueField R)] in
/-- The proved recurrence is the actual mathlib inverse local polynomial,
whenever its arithmetic identification has been established. -/
theorem localPowerSeries_eq_localSeries (W : WeierstrassCurve K) (a q : ℤ)
    (hpoly : W.localPolynomial R =
      1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2) :
    W.localPowerSeries R = localSeries a q := by
  have hp : (W.localPolynomial R : PowerSeries ℤ) =
      1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2 := by
    rw [hpoly]
    simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  unfold WeierstrassCurve.localPowerSeries
  apply left_inv_eq_right_inv (a := (W.localPolynomial R : PowerSeries ℤ))
  · apply PowerSeries.invOfUnit_mul
    rw [hp]
    simp
  · rw [hp]
    exact localSeries_inverse a q

theorem localCoefficient_eq_localPowerSeries (e : (WeierstrassCurve ℤ)) (p : ℕ)
    [Fact p.Prime] (W : WeierstrassCurve K)
    (k : IsLocalRing.ResidueField R ≃+* ZMod p)
    (hmodel : ((W.minimal R).reduction R).map k.toRingHom = WeierstrassCurve.baseChange e (ZMod p)) (n : ℕ) :
    localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic n =
      PowerSeries.coeff n (W.localPowerSeries R) := by
  rw [localPowerSeries_eq_localSeries W _ _ (localPolynomial_eq_modelFactor e p W k hmodel)]
  exact (localSeries_correct _ _ _).symm

/-- The local formal Dirichlet factor at p^n is the executable recurrence
coefficient, once a minimal-reduction identification is supplied. -/
theorem localEulerFactor_apply_pow_eq (e : (WeierstrassCurve ℤ)) (p : ℕ)
    [Fact p.Prime] (W : WeierstrassCurve K)
    (k : IsLocalRing.ResidueField R ≃+* ZMod p)
    (hmodel : ((W.minimal R).reduction R).map k.toRingHom = WeierstrassCurve.baseChange e (ZMod p)) (n : ℕ) :
    W.localEulerFactor R (p ^ n) =
      localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic n := by
  have hc : Nat.card (IsLocalRing.ResidueField R) = p := by
    rw [Nat.card_congr k.toEquiv]
    simp [Nat.card_eq_fintype_card]
  rw [WeierstrassCurve.localEulerFactor, hc,
    ArithmeticFunction.ofPowerSeries_apply_pow (Fact.out : p.Prime).one_lt]
  exact (localCoefficient_eq_localPowerSeries e p W k hmodel n).symm

end Local

/-- TauCeti's global multiplicativity reduces the entire coefficient bridge to
prime-power coefficients. The latter remain genuine arithmetic proof inputs. -/
theorem curveCoefficient_eq_euler (e : (WeierstrassCurve ℤ))
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic k) (n : ℕ) :
    (WeierstrassCurve.baseChange e ℚ).LFunction n = eulerCoefficient (modelFactor e) n := by
  by_cases hn : n = 0
  · simp [hn, eulerCoefficient]
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (WeierstrassCurve.baseChange e ℚ).isMultiplicative_LFunction hn, eulerCoefficient, ite_eq_right hn]
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  exact hl p (Nat.prime_of_mem_primeFactors hp) _

/-- Actual-curve coefficient bounds follow from the proved arithmetic bridge;
no bound is included in the modularity axiom. -/
theorem curveCoefficient_abs_le_cube (e : (WeierstrassCurve ℤ))
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic k) (n : ℕ) :
    |(WeierstrassCurve.baseChange e ℚ).LFunction n| ≤ (n : ℤ) ^ 3 := by
  rw [curveCoefficient_eq_euler e hl n]
  exact model_eulerCoefficient_abs_le_cube e n

/-- Prefix equality uses actual coefficients and does not inspect reference
ranks or a supplied conductor. -/
theorem modelCoefficients_eq_curve (e : (WeierstrassCurve ℤ))
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ k) =
        localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic k) (limit : ℕ) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j + 1)) := by
  rw [modelCoefficients_eq_euler]
  apply List.map_congr_left
  intro j _
  exact (curveCoefficient_eq_euler e hl _).symm

end VerifiedLcalc.EllipticCurve
