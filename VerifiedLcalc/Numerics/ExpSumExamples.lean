module

public import VerifiedLcalc.Numerics.ExpSumCore

@[expose] public section

namespace VerifiedLcalc.Numerics.Examples

/-- A finite exponential sum with mixed-sign coefficients. It tests numerical
composition, and is not asserted to be an elliptic-curve L-value. -/
def signedTerms : List WeightedExpTerm :=
  [⟨1, Dyadic.ofIntWithPrec (-1) 0⟩, ⟨-2, Dyadic.ofIntWithPrec (-2) 0⟩]

/-- The computed bounds remain separated with a small independently supplied
error allowance. The validity of any actual analytic error is a separate proof. -/
theorem signedTerms_separated :
    (expSumBox signedTerms 24 (1 / 10000)).excludesZero = true := by decide +kernel

/-- A large uncertainty must not certify nonvanishing. -/
theorem signedTerms_uncertain :
    (expSumBox signedTerms 24 1).excludesZero = false := by decide +kernel

/-- Coefficient zero must contribute zero, independently of the enclosure. -/
example : weightedExpBounds ⟨0, Dyadic.ofIntWithPrec 7 0⟩ 12 = (0, 0) := by decide +kernel

end VerifiedLcalc.Numerics.Examples
