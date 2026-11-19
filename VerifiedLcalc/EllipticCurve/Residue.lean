module

public import VerifiedLcalc.EllipticCurve.GlobalCoefficients

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The actual residue field of a rational-number-field prime, as a prime
field of its proved norm. The isomorphism is built from ideal quotients. -/
noncomputable def idealQuotientEquivZMod (v : HeightOneSpectrum (𝓞 ℚ)) :
    (𝓞 ℚ ⧸ v.asIdeal) ≃+* ZMod v.asIdeal.absNorm := by
  let vi := RationalPrimes.integerPlace v
  have hi : vi.asIdeal = Ideal.span {(v.asIdeal.absNorm : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self vi.asIdeal, RationalPrimes.norm_integerPlace]
  exact (Ideal.quotientEquiv v.asIdeal vi.asIdeal Rat.ringOfIntegersEquiv
    (RationalPrimes.integerPlace_asIdeal v)).trans
      ((Ideal.quotEquivOfEq hi).trans (Int.quotientSpanNatEquivZMod _))

/-- An explicit field isomorphism for the residue field used by the local Euler
factor at an ordinary rational prime p. -/
noncomputable def completionResidueEquiv (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField ((rationalPlace p).adicCompletionIntegers ℚ) ≃+* ZMod p := by
  have k := ((rationalPlace p).residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
    (idealQuotientEquivZMod (rationalPlace p))
  exact (congrArg (fun n : ℕ =>
    IsLocalRing.ResidueField ((rationalPlace p).adicCompletionIntegers ℚ) ≃+* ZMod n)
      (rationalPlace_norm p)).mp k

end VerifiedLcalc.EllipticCurve
