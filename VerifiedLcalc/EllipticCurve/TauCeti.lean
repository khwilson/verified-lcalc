module

public import VerifiedLcalc.EllipticCurve.Correctness
public import VerifiedLcalc.EllipticCurve.Euler
public import VerifiedLcalc.EllipticCurve.Bounds
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Our enumerator agrees with TauCeti's projective-model count, including at
singular reduction. -/
theorem pointCount_eq_tauceti (e : Artifacts.CurveEquation) (p : ℕ) [Fact p.Prime] :
    pointCount e p = (weierstrass e (ZMod p)).pointCount := by
  rw [pointCount_correct, WeierstrassCurve.pointCount_def]
  rfl

theorem frobeniusTrace_eq_tauceti (e : Artifacts.CurveEquation) (p : ℕ) [Fact p.Prime] :
    frobeniusTrace e p = (weierstrass e (ZMod p)).frobeniusTrace := by
  rw [frobeniusTrace, pointCount_eq_tauceti, WeierstrassCurve.frobeniusTrace_def]
  simp [Nat.card_eq_fintype_card]

/-- Transport the projective equation count through an actual residue-field
isomorphism; singular points remain included. -/
theorem pointCount_map_equiv {F K : Type*} [Field F] [Field K]
    (W : WeierstrassCurve F) (k : F ≃+* K) :
    (W.map k.toRingHom).pointCount = W.pointCount := by
  rw [WeierstrassCurve.pointCount_def, WeierstrassCurve.pointCount_def]
  congr 1
  apply Nat.card_congr
  exact ((k.toEquiv.prodCongr k.toEquiv).subtypeEquiv
    (fun xy => (W.toAffine.map_equation (f := k.toRingHom) k.injective xy.1 xy.2).symm)).symm

theorem frobeniusTrace_map_equiv {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    (W : WeierstrassCurve F) (k : F ≃+* K) :
    (W.map k.toRingHom).frobeniusTrace = W.frobeniusTrace := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.frobeniusTrace_def,
    pointCount_map_equiv, Nat.card_congr k.toEquiv]

section Local
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [Finite (IsLocalRing.ResidueField R)]

/-- The arithmetic bridge requires an identification with the reduction of a
minimal local model. No arbitrary input model is silently declared minimal. -/
theorem localPolynomial_eq_modelFactor (e : Artifacts.CurveEquation) (p : ℕ)
    [Fact p.Prime] (W : WeierstrassCurve K)
    (k : IsLocalRing.ResidueField R ≃+* ZMod p)
    (hmodel : ((W.minimal R).reduction R).map k.toRingHom = weierstrass e (ZMod p)) :
    W.localPolynomial R =
      1 - Polynomial.C (modelFactor e p).trace * Polynomial.X +
        Polynomial.C (modelFactor e p).quadratic * Polynomial.X ^ 2 := by
  have ht : ((W.minimal R).reduction R).frobeniusTrace = frobeniusTrace e p := by
    rw [frobeniusTrace_eq_tauceti, ← hmodel, frobeniusTrace_map_equiv]
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

theorem localCoefficient_eq_localPowerSeries (e : Artifacts.CurveEquation) (p : ℕ)
    [Fact p.Prime] (W : WeierstrassCurve K)
    (k : IsLocalRing.ResidueField R ≃+* ZMod p)
    (hmodel : ((W.minimal R).reduction R).map k.toRingHom = weierstrass e (ZMod p)) (n : ℕ) :
    localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic n =
      PowerSeries.coeff n (W.localPowerSeries R) := by
  rw [localPowerSeries_eq_localSeries W _ _ (localPolynomial_eq_modelFactor e p W k hmodel)]
  exact (localSeries_correct _ _ _).symm

/-- The local formal Dirichlet factor at p^n is the executable recurrence
coefficient, once a minimal-reduction identification is supplied. -/
theorem localEulerFactor_apply_pow_eq (e : Artifacts.CurveEquation) (p : ℕ)
    [Fact p.Prime] (W : WeierstrassCurve K)
    (k : IsLocalRing.ResidueField R ≃+* ZMod p)
    (hmodel : ((W.minimal R).reduction R).map k.toRingHom = weierstrass e (ZMod p)) (n : ℕ) :
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
theorem curveCoefficient_eq_euler (e : Artifacts.CurveEquation)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (weierstrass e ℚ).LFunction (p ^ k) =
        localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic k) (n : ℕ) :
    (weierstrass e ℚ).LFunction n = eulerCoefficient (modelFactor e) n := by
  by_cases hn : n = 0
  · simp [hn, eulerCoefficient]
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (weierstrass e ℚ).isMultiplicative_LFunction hn, eulerCoefficient, ite_eq_right hn]
  unfold Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  exact hl p (Nat.prime_of_mem_primeFactors hp) _

/-- Actual-curve coefficient bounds follow from the proved arithmetic bridge;
no bound is included in the modularity axiom. -/
theorem curveCoefficient_abs_le_cube (e : Artifacts.CurveEquation)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (weierstrass e ℚ).LFunction (p ^ k) =
        localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic k) (n : ℕ) :
    |(weierstrass e ℚ).LFunction n| ≤ (n : ℤ) ^ 3 := by
  rw [curveCoefficient_eq_euler e hl n]
  exact model_eulerCoefficient_abs_le_cube e n

/-- Prefix equality uses actual coefficients and does not inspect reference
ranks or a supplied conductor. -/
theorem modelCoefficients_eq_curve (e : Artifacts.CurveEquation)
    (hl : ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      (weierstrass e ℚ).LFunction (p ^ k) =
        localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic k) (limit : ℕ) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => (weierstrass e ℚ).LFunction (j + 1)) := by
  rw [modelCoefficients_eq_euler]
  apply List.map_congr_left
  intro j _
  exact (curveCoefficient_eq_euler e hl _).symm

end VerifiedLcalc.EllipticCurve
