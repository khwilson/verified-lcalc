module

public import VerifiedLcalc.EllipticCurve.LocalModel
public import VerifiedLcalc.EllipticCurve.Residue

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- Any locally minimal input equation gives the actual Euler polynomial,
including additive reduction and residue characteristics two and three. -/
theorem minimal_localPolynomial (e : Artifacts.CurveEquation)
    (hn : discriminant e ≠ 0)
    (p : ℕ) [Fact p.Prime]
    (hmin : WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((weierstrass e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ))) :
    ((weierstrass e ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPlace p).adicCompletionIntegers ℚ) =
      1 - Polynomial.C (modelFactor e p).trace * Polynomial.X +
        Polynomial.C (modelFactor e p).quadratic * Polynomial.X ^ 2 := by
  classical
  let v := rationalPlace p
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := weierstrass e R
  let U := W.baseChange K
  let k := completionResidueEquiv p
  have hU : U = (weierstrass e ℚ).baseChange K := by
    simp only [U, W, WeierstrassCurve.baseChange, weierstrass_map]
  let : WeierstrassCurve.IsMinimal R U := hmin
  let : U.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    rw [show U = weierstrass e K by simp only [U, W, WeierstrassCurve.baseChange, weierstrass_map],
      weierstrass_discriminant]
    exact_mod_cast hn
  have hinput : (W.map (IsLocalRing.residue R)).map k.toRingHom = weierstrass e (ZMod p) := by
    simp only [W, weierstrass_map]
  have ht : (W.map (IsLocalRing.residue R)).frobeniusTrace = frobeniusTrace e p := by
    rw [frobeniusTrace_eq_tauceti, ← hinput, frobeniusTrace_map_equiv]
  have hg : (W.map (IsLocalRing.residue R)).Δ ≠ 0 ↔ goodReduction e p = true := by
    rw [goodReduction_correct, ← hinput, WeierstrassCurve.map_Δ]
    constructor
    · intro h hzero
      exact h (k.injective (by simpa using hzero))
    · intro h hzero
      apply h
      simp [hzero]
  have hc : Nat.card (IsLocalRing.ResidueField R) = p := by
    rw [completion_residue_card, rationalPlace_norm]
  have hq : (if (W.map (IsLocalRing.residue R)).Δ ≠ 0 then (p : ℤ) else 0) =
      (modelFactor e p).quadratic := by
    by_cases hgood : goodReduction e p = true
    · rw [ite_eq_left (hg.mpr hgood)]
      simp [modelFactor, hgood]
    · rw [ite_eq_right (mt hg.mp hgood)]
      simp [modelFactor, hgood]
  have h := localPolynomial_of_minimal_input (K := K) W
  rw [ht, hc, hq] at h
  change U.localPolynomial R = _ at h
  rw [hU] at h
  exact h

/-- Full prime-power identification, proved for every locally minimal model. -/
theorem minimal_primePower (e : Artifacts.CurveEquation)
    (hn : discriminant e ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((weierstrass e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
          ((rationalPlace p).adicCompletion ℚ)))
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (weierstrass e ℚ).LFunction (p ^ j) =
      localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic j := by
  let : Fact p.Prime := ⟨hp⟩
  rw [LFunction_apply_prime_pow, localPowerSeries_eq_localSeries _ _ _
    (minimal_localPolynomial e hn p (hmin p))]
  exact localSeries_correct _ _ _

/-- The executable coefficient table is the actual curve coefficient prefix,
with no trace-size restriction or modularity assumption. -/
theorem minimal_prefix (e : Artifacts.CurveEquation)
    (hn : discriminant e ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((weierstrass e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
          ((rationalPlace p).adicCompletion ℚ))) (limit : ℕ) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => (weierstrass e ℚ).LFunction (j + 1)) :=
  modelCoefficients_eq_curve e (minimal_primePower e hn hmin) limit

end VerifiedLcalc.EllipticCurve
