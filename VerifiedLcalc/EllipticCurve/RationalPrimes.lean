module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

@[expose] public section
namespace VerifiedLcalc.RationalPrimes
open NumberField IsDedekindDomain

/-- Transport a rational-number-field prime ideal to an actual integer prime
ideal, using mathlib's ring-of-integers equivalence. -/
noncomputable def integerPlace (v : HeightOneSpectrum (𝓞 ℚ)) : HeightOneSpectrum ℤ :=
  HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv v

theorem integerPlace_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    (integerPlace v).asIdeal = v.asIdeal.map Rat.ringOfIntegersEquiv.toRingHom := by
  change v.asIdeal.comap Rat.ringOfIntegersEquiv.symm.toRingHom = _
  exact Ideal.comap_symm Rat.ringOfIntegersEquiv

/-- The ideal norm is unchanged by transporting from O_Q to Z. -/
theorem norm_integerPlace (v : HeightOneSpectrum (𝓞 ℚ)) :
    (integerPlace v).asIdeal.absNorm = v.asIdeal.absNorm := by
  rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal (integerPlace v).asIdeal
    Rat.ringOfIntegersEquiv (integerPlace_asIdeal v)).symm.toEquiv

theorem norm_prime (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal.absNorm.Prime := by
  rw [← norm_integerPlace, Int.prime_absNorm]
  exact (Ideal.prime_iff_isPrime (integerPlace v).ne_bot).mpr (integerPlace v).isPrime

/-- A rational prime ideal is uniquely determined by its residue norm. -/
theorem norm_injective : Function.Injective
    (fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal.absNorm) := by
  intro v w h
  change v.asIdeal.absNorm = w.asIdeal.absNorm at h
  have hi : integerPlace v = integerPlace w := by
    apply HeightOneSpectrum.ext
    rw [← Int.ideal_span_absNorm_eq_self (integerPlace v).asIdeal,
      ← Int.ideal_span_absNorm_eq_self (integerPlace w).asIdeal,
      norm_integerPlace, norm_integerPlace, h]
  exact (HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).injective hi

end VerifiedLcalc.RationalPrimes
