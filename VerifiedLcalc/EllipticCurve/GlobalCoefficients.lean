module

public import VerifiedLcalc.EllipticCurve.EulerProduct
public import VerifiedLcalc.EllipticCurve.RationalPrimes
public import VerifiedLcalc.EllipticCurve.TauCeti
public import VerifiedLcalc.Upstream.TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Data.ZMod.QuotientRing

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The residue cardinality in mathlib's local factor is the actual ideal norm. -/
theorem completion_residue_card (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = v.asIdeal.absNorm := by
  rw [Ideal.absNorm_eq_natCard]
  exact (Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := ℚ)).toEquiv).symm

/-- A genuine rational prime ideal with norm p. No numerical conductor or
reference rank is used in its construction. -/
noncomputable def rationalPlace (p : ℕ) [Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  (HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).symm
    { asIdeal := Ideal.span {(p : ℤ)}
      isPrime := (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
        (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime)))
      ne_bot := by simp [(Fact.out : p.Prime).ne_zero] }

theorem rationalPlace_norm (p : ℕ) [Fact p.Prime] : (rationalPlace p).asIdeal.absNorm = p := by
  rw [← RationalPrimes.norm_integerPlace]
  have hi : RationalPrimes.integerPlace (rationalPlace p) =
      ({ asIdeal := Ideal.span {(p : ℤ)}
         isPrime := (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
           (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime)))
         ne_bot := by simp [(Fact.out : p.Prime).ne_zero] } : HeightOneSpectrum ℤ) := by
    exact Equiv.apply_symm_apply _ _
  rw [hi]
  simp

/-- The global prime-power coefficient is the corresponding local power-series
coefficient. This discharges Euler-product extraction for Q. -/
theorem LFunction_apply_norm_pow (W : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    W.LFunction (v.asIdeal.absNorm ^ k) =
      PowerSeries.coeff k ((W.baseChange (v.adicCompletion ℚ)).localPowerSeries
        (v.adicCompletionIntegers ℚ)) := by
  let f := fun v : HeightOneSpectrum (𝓞 ℚ) =>
    (W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)
  have h := EulerProduct.apply_prime_pow (fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal.absNorm)
    f (fun v => (W.baseChange (v.adicCompletion ℚ)).constantCoeff_localPowerSeries
      (v.adicCompletionIntegers ℚ)) v (RationalPrimes.norm_prime v) (by
        intro w hne
        exact (Nat.coprime_primes (RationalPrimes.norm_prime w) (RationalPrimes.norm_prime v)).mpr
          (fun he => hne (RationalPrimes.norm_injective he))) k
  simp only [WeierstrassCurve.LFunction, WeierstrassCurve.localEulerFactor,
    completion_residue_card]
  convert h using 1
  apply congrArg (fun g : HeightOneSpectrum (𝓞 ℚ) → ArithmeticFunction ℤ =>
    ArithmeticFunction.eulerProduct g (v.asIdeal.absNorm ^ k))
  funext u
  congr 2
  unfold WeierstrassCurve.baseChange
  congr 1
  exact Subsingleton.elim _ _

/-- The extraction theorem indexed by an ordinary rational prime. -/
theorem LFunction_apply_prime_pow (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] (k : ℕ) :
    W.LFunction (p ^ k) = PowerSeries.coeff k
      ((W.baseChange ((rationalPlace p).adicCompletion ℚ)).localPowerSeries
        ((rationalPlace p).adicCompletionIntegers ℚ)) := by
  simpa only [rationalPlace_norm] using LFunction_apply_norm_pow W (rationalPlace p) k

end VerifiedLcalc.EllipticCurve
