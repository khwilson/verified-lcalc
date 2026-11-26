import CertifiedCurves

-- Import only: no JSON file is read and no certificate command runs here.
open VerifiedLcalc VerifiedLcalc.Modularity

theorem curve37_rank :
    analyticOrderAt (modularWitness Curve37.curve Curve37.nonsingular).formL (1 : ℂ) = 1 :=
  Curve37.analytic_rank

#check Curve11.analytic_rank
#check Curve112.analytic_rank
#print axioms curve37_rank
#reduce Curve37.certifiedRank.val

theorem curve37_coefficients :
    (List.range 12).map (fun n => (Curve37.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, -2, -3, 2, -2, 6, -1, 0, 6, 4, -5, -6] :=
  Curve37.l_function_coefficients

theorem curve37_certificate_coefficients :
    (List.range 12).map (fun n => (Curve37.curve.baseChange ℚ).LFunction (n + 1)) =
      [1, -2, -3, 2, -2, 6, -1, 0, 6, 4, -5, -6] :=
  (Curve37.certificate.arithmetic.dirichletCoefficients.get (by rfl)).property

#check Curve11.l_function_coefficients
#print axioms curve37_coefficients
#print axioms curve37_certificate_coefficients
