import VerifiedLcalcTests.Arithmetic.ReductionExamples

/-- info: 'VerifiedLcalc.EllipticCurve.ReductionExamples.C32_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.ReductionExamples.C32_a4.coefficients_correct

#check VerifiedLcalc.EllipticCurve.ReductionExamples.curve32_coefficient_four
#reduce VerifiedLcalc.EllipticCurve.modelCoefficients
  VerifiedLcalc.EllipticCurve.ReductionExamples.C32_a4.equation 8
