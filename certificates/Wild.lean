import VerifiedLcalc.Certificates.Batch.C27_a1
import VerifiedLcalc.Certificates.Batch.C32_a4
import VerifiedLcalc.Certificates.Batch.C36_a1
import VerifiedLcalc.Certificates.NegativeSigns
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

-- Execute values whose types carry already checked exact analytic-rank proofs.
#eval Certificates.Batch.C27_a1.certifiedRank.val
#eval Certificates.Batch.C32_a4.certifiedRank.val
#eval Certificates.Batch.C36_a1.certifiedRank.val

-- This separate subtype carries only a lower-bound proof, never an exact rank.
def negativeBound : {n : ℕ // n ≤ analyticOrderAt
    (modularWitness Certificates.NegativeSigns.C112_a1.equation
      Certificates.NegativeSigns.C112_a1.nonsingular).formL (1 : ℂ)} :=
  ⟨1, Certificates.NegativeSigns.C112_a1.analytic_rank_at_least_one⟩
#eval negativeBound.val
