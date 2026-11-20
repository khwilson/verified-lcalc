module

public import VerifiedLcalc.UpstreamCandidates.TauCeti.LocalModel
public import VerifiedLcalc.EllipticCurve.Residue

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- Any locally minimal input equation gives the actual Euler polynomial,
including additive reduction and residue characteristics two and three. -/
theorem minimal_localPolynomial (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0)
    (p : ℕ) [Fact p.Prime]
    (hmin : WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
      ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
        ((rationalPlace p).adicCompletion ℚ))) :
    ((WeierstrassCurve.baseChange e ℚ).baseChange ((rationalPlace p).adicCompletion ℚ)).localPolynomial
      ((rationalPlace p).adicCompletionIntegers ℚ) =
      1 - Polynomial.C (modelFactor e p).trace * Polynomial.X +
        Polynomial.C (modelFactor e p).quadratic * Polynomial.X ^ 2 := by
  classical
  let v := rationalPlace p
  let K := v.adicCompletion ℚ
  let R := v.adicCompletionIntegers ℚ
  let W := WeierstrassCurve.baseChange e R
  let U := W.baseChange K
  let k := completionResidueEquiv p
  have hU : U = (WeierstrassCurve.baseChange e ℚ).baseChange K := by
    ext <;> simp [U, W, WeierstrassCurve.baseChange]
  let : WeierstrassCurve.IsMinimal R U := hmin
  let : U.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    have hUK : U = WeierstrassCurve.baseChange e K := by
      ext <;> simp [U, W, WeierstrassCurve.baseChange]
    rw [hUK, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    rw [show algebraMap ℤ K = Int.castRingHom K from Subsingleton.elim _ _]
    change (e.Δ : K) ≠ 0
    exact_mod_cast hn
  have hinput : (W.map (IsLocalRing.residue R)).map k.toRingHom = WeierstrassCurve.baseChange e (ZMod p) := by
    ext <;> simp [W, WeierstrassCurve.baseChange]
  have ht : (W.map (IsLocalRing.residue R)).frobeniusTrace = computeFrobeniusTrace e p := by
    rw [computeFrobeniusTrace_correct, ← hinput, WeierstrassCurve.frobeniusTrace_map_equiv]
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
  have h := WeierstrassCurve.localPolynomial_of_minimal_input (K := K) W
  rw [ht, hc, hq] at h
  change U.localPolynomial R = _ at h
  rw [hU] at h
  exact h

/-- Full prime-power identification, proved for every locally minimal model. -/
theorem minimal_primePower (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
          ((rationalPlace p).adicCompletion ℚ)))
    (p : ℕ) (hp : p.Prime) (j : ℕ) :
    (WeierstrassCurve.baseChange e ℚ).LFunction (p ^ j) =
      localCoefficient (modelFactor e p).trace (modelFactor e p).quadratic j := by
  let : Fact p.Prime := ⟨hp⟩
  rw [LFunction_apply_prime_pow, localPowerSeries_eq_localSeries _ _ _
    (minimal_localPolynomial e hn p (hmin p))]
  exact localSeries_correct _ _ _

/-- The executable coefficient table is the actual curve coefficient prefix,
with no trace-size restriction or modularity assumption. -/
theorem minimal_prefix (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0)
    (hmin : ∀ (p : ℕ) [Fact p.Prime],
      WeierstrassCurve.IsMinimal ((rationalPlace p).adicCompletionIntegers ℚ)
        ((WeierstrassCurve.baseChange e ((rationalPlace p).adicCompletionIntegers ℚ)).baseChange
          ((rationalPlace p).adicCompletion ℚ))) (limit : ℕ) :
    modelCoefficients e limit = (List.range limit).map
      (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j + 1)) :=
  modelCoefficients_eq_curve e (minimal_primePower e hn hmin) limit

end VerifiedLcalc.EllipticCurve
