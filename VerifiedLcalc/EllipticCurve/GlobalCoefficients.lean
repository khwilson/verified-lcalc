module

public import VerifiedLcalc.EllipticCurve.EulerProduct
public import VerifiedLcalc.EllipticCurve.RationalPrimes
public import VerifiedLcalc.EllipticCurve.TauCeti
public import VerifiedLcalc.EllipticCurve.RationalPlace
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Data.ZMod.QuotientRing

/-! # Local and global coefficients at rational primes -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The residue cardinality in mathlib's local factor is the actual ideal norm. -/
theorem completion_residue_card (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = v.asIdeal.absNorm := by
  rw [Ideal.absNorm_eq_natCard]
  exact (Nat.card_congr (v.residueFieldEquivAdicCompletionIntegers (K := ℚ)).toEquiv).symm

theorem rationalPlace_norm (p : ℕ) [Fact p.Prime] : (rationalPlace p).asIdeal.absNorm = p := by
  rw [rationalPlace, Rat.HeightOneSpectrum.absNorm_asIdeal]
  change (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩)).val = p
  exact congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

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
