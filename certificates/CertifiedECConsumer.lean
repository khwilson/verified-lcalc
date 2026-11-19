import CertifiedCurves

-- Import only: no JSON file is read and no certificate command runs here.
open VerifiedLcalc VerifiedLcalc.Assumptions

theorem curve37_rank :
    analyticOrderAt (modularWitness Curve37.curve Curve37.nonsingular).formL (1 : ℂ) = 1 :=
  Curve37.analytic_rank

#check Curve11.analytic_rank
#check Curve112.analytic_rank
#print axioms curve37_rank
#eval Curve37.certifiedRank.val
