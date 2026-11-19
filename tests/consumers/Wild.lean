import VerifiedLcalcTests.Fixtures.NegativeSigns
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Modularity

-- This separate subtype carries only a lower-bound proof, never an exact rank.
def negativeBound : {n : ℕ // n ≤ analyticOrderAt
    (modularWitness VerifiedLcalcTests.Fixtures.NegativeSigns.C112_a1.equation
      VerifiedLcalcTests.Fixtures.NegativeSigns.C112_a1.nonsingular).formL (1 : ℂ)} :=
  ⟨1, VerifiedLcalcTests.Fixtures.NegativeSigns.C112_a1.analytic_rank_at_least_one⟩
#reduce negativeBound.val
