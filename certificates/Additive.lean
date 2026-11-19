import VerifiedLcalc.EllipticCurve.ReductionExamples

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a4.coefficients_correct

#check VerifiedLcalc.EllipticCurve.ReductionExamples.curve32_coefficient_four
#eval VerifiedLcalc.EllipticCurve.modelCoefficients
  VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a4.equation 8
