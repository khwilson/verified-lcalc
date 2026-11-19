import VerifiedLcalc.EllipticCurve.Bounds
import VerifiedLcalc.Numerics.MellinSplit
import VerifiedLcalc.EllipticCurve.CentralExamples
import VerifiedLcalc.Certificates.Curve11Central
import VerifiedLcalc.Certificates.NumericalQuartic
import VerifiedLcalc.Examples
import VerifiedLcalc.Lmfdb
import VerifiedLcalc.Certificates.Cubic
import VerifiedLcalc.Certificates.Curve11Arithmetic
import VerifiedLcalc.Numerics.Dyadic
import VerifiedLcalc.Numerics.ExpSum
import VerifiedLcalc.Numerics.ExpSumExamples
import VerifiedLcalc.EllipticCurve.ReductionExamples
import VerifiedLcalc.EllipticCurve.ArithmeticExamples
import VerifiedLcalc.Assumptions.NegativeSign
import VerifiedLcalc.Assumptions.Regression
import VerifiedLcalc.Certificates.AssumedCurve11
import VerifiedLcalc.Assumptions.Certificates
import VerifiedLcalc.Certificates.AssumedCurve37
import VerifiedLcalc.Assumptions.DerivativeCertification
import VerifiedLcalc.Assumptions.GeneratedRankOne
import VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples
import VerifiedLcalc.EllipticCurve.BadPrimeExamples
import VerifiedLcalc.EllipticCurve.InvariantMinimality
import VerifiedLcalc.LmfdbSupplementProofs
import VerifiedLcalc.Assumptions.FastSign
import VerifiedLcalc.Certificates.GeneralModularityExamples
import VerifiedLcalc.Assumptions.Prefix
import VerifiedLcalc.Assumptions.CentralEvaluator
import VerifiedLcalc.Assumptions.TameCertification
import VerifiedLcalc.Assumptions.TameNegativeSign
import VerifiedLcalc.EllipticCurve.WildExamples
import VerifiedLcalc.EllipticCurve.WildExpandedExamples
import VerifiedLcalc.Assumptions.WildCertification
import VerifiedLcalc.Certificates.Batch.C27_a1

#print axioms VerifiedLcalc.Box.valid_correct
#print axioms VerifiedLcalc.Box.isZero_correct
#print axioms VerifiedLcalc.Box.excludesZero_correct
#print axioms VerifiedLcalc.scan_correct
#print axioms VerifiedLcalc.certify_correct
#print axioms VerifiedLcalc.Box.isZero_sound
#print axioms VerifiedLcalc.Box.excludesZero_sound
#print axioms VerifiedLcalc.Witness.sound
#print axioms VerifiedLcalc.scan_analyticOrderAt
#print axioms VerifiedLcalc.computeRank_correct
#print axioms VerifiedLcalc.Examples.cubic_rank
#print axioms VerifiedLcalc.Examples.cubicResult_correct


#print axioms VerifiedLcalc.Regression.checkCase_correct
#print axioms VerifiedLcalc.Regression.pendingBackend_correct
#print axioms VerifiedLcalc.Lmfdb.has_100_cases
#print axioms VerifiedLcalc.Lmfdb.distinct_labels
#print axioms VerifiedLcalc.Lmfdb.ranks_covered

#print axioms VerifiedLcalc.Artifacts.Subject.center_correct
#print axioms VerifiedLcalc.Artifacts.check_correct
#print axioms VerifiedLcalc.Artifacts.check_request_eq
#print axioms VerifiedLcalc.Artifacts.validate_correct
#print axioms VerifiedLcalc.Artifacts.check_sound
#print axioms VerifiedLcalc.Artifacts.check_monomial_sound
#print axioms VerifiedLcalc.Artifacts.ellipticCurve_not_denotes
#print axioms VerifiedLcalc.Examples.cubicArtifact_rank
#print axioms VerifiedLcalc.Examples.firstCurve_no_evidence
#print axioms VerifiedLcalc.Certificates.Cubic.certified_analytic_order


#print axioms VerifiedLcalc.Regression.CurveInput.equation_correct
#print axioms VerifiedLcalc.EllipticCurve.weierstrass_correct
#print axioms VerifiedLcalc.EllipticCurve.b2_correct
#print axioms VerifiedLcalc.EllipticCurve.b4_correct
#print axioms VerifiedLcalc.EllipticCurve.b6_correct
#print axioms VerifiedLcalc.EllipticCurve.b8_correct
#print axioms VerifiedLcalc.EllipticCurve.discriminant_correct
#print axioms VerifiedLcalc.EllipticCurve.residual_correct
#print axioms VerifiedLcalc.EllipticCurve.onCurve_correct
#print axioms VerifiedLcalc.EllipticCurve.onCurve_equation
#print axioms VerifiedLcalc.EllipticCurve.affinePoints_correct
#print axioms VerifiedLcalc.EllipticCurve.affinePoints_nodup
#print axioms VerifiedLcalc.EllipticCurve.affineCount_correct
#print axioms VerifiedLcalc.EllipticCurve.pointCount_correct
#print axioms VerifiedLcalc.EllipticCurve.frobeniusTrace_correct
#print axioms VerifiedLcalc.EllipticCurve.isPrime_correct
#print axioms VerifiedLcalc.EllipticCurve.goodReduction_correct
#print axioms VerifiedLcalc.EllipticCurve.analysePrime_correct
#print axioms VerifiedLcalc.EllipticCurve.analysePrime_sound
#print axioms VerifiedLcalc.EllipticCurve.pointCount_eq_card_point
#print axioms VerifiedLcalc.EllipticCurve.localPair_correct
#print axioms VerifiedLcalc.EllipticCurve.localCoefficient_correct
#print axioms VerifiedLcalc.EllipticCurve.localCoefficient_unique
#print axioms VerifiedLcalc.EllipticCurve.localSeries_correct
#print axioms VerifiedLcalc.EllipticCurve.localSeries_inverse
#print axioms VerifiedLcalc.Certificates.Curve11Arithmetic.point_count_two
#print axioms VerifiedLcalc.Certificates.Curve11Arithmetic.trace_two
#print axioms VerifiedLcalc.Certificates.Curve11Arithmetic.euler_factor_two
#print axioms VerifiedLcalc.Numerics.boxOfDyadics_correct
#print axioms VerifiedLcalc.Numerics.rational_bound
#print axioms VerifiedLcalc.Numerics.square_bound

#print axioms Inclusion.IntervalDyadicReal.expBounds_bounds
#print axioms Inclusion.IntervalDyadicReal.exp_mem
#print axioms VerifiedLcalc.Numerics.exponentialBox_correct
#print axioms VerifiedLcalc.Numerics.exp_one_enclosure
#print axioms VerifiedLcalc.Numerics.exp_neg_one_enclosure
#print axioms VerifiedLcalc.Numerics.exp_negative_interval
#print axioms VerifiedLcalc.Numerics.weightedExpBounds_correct
#print axioms VerifiedLcalc.Numerics.expSumBounds_correct
#print axioms VerifiedLcalc.Numerics.expSumBox_correct
#print axioms VerifiedLcalc.Numerics.analyticOrder_zero_of_expSum
#print axioms VerifiedLcalc.Numerics.Examples.signedTerms_separated
#print axioms VerifiedLcalc.Numerics.Examples.signedTerms_uncertain

#print axioms VerifiedLcalc.PrecisionPolicy.cutoff_correct
#print axioms VerifiedLcalc.globalPrecision_correct
#print axioms VerifiedLcalc.Box.withinCutoff_correct
#print axioms VerifiedLcalc.Box.withinCutoff_sound
#print axioms VerifiedLcalc.NumericalRanks.check_correct
#print axioms VerifiedLcalc.NumericalRanks.check_request_eq
#print axioms VerifiedLcalc.NumericalRanks.validate_correct
#print axioms VerifiedLcalc.NumericalRanks.enclosures_small
#print axioms VerifiedLcalc.NumericalRanks.check_sound
#print axioms VerifiedLcalc.NumericalRanks.check_conditional_lowerBound
#print axioms VerifiedLcalc.Certificates.NumericalQuartic.checked
#print axioms VerifiedLcalc.Certificates.NumericalQuartic.certified_small_derivatives
#print axioms VerifiedLcalc.Certificates.NumericalQuartic.conditional_analytic_lower_bound
#print axioms VerifiedLcalc.Certificates.NumericalQuartic.small_does_not_imply_rank_four

#print axioms VerifiedLcalc.Numerics.rationalExpBounds_correct
#print axioms VerifiedLcalc.Numerics.rationalWeightedBounds_correct
#print axioms VerifiedLcalc.Numerics.rationalExpSumBounds_correct
#print axioms VerifiedLcalc.EllipticCurve.valuationFuel_correct
#print axioms VerifiedLcalc.EllipticCurve.primeExponent_correct
#print axioms VerifiedLcalc.EllipticCurve.modelFactor_correct
#print axioms VerifiedLcalc.EllipticCurve.modelFactors_correct
#print axioms VerifiedLcalc.EllipticCurve.modelFactors_prime
#print axioms VerifiedLcalc.EllipticCurve.coefficientFromFactors_correct
#print axioms VerifiedLcalc.EllipticCurve.modelCoefficients_correct
#print axioms VerifiedLcalc.EllipticCurve.modelCoefficients_euler
#print axioms VerifiedLcalc.EllipticCurve.piBounds_correct
#print axioms VerifiedLcalc.EllipticCurve.alphaBounds_correct
#print axioms VerifiedLcalc.EllipticCurve.centralTerms_correct
#print axioms VerifiedLcalc.EllipticCurve.centralBox_correct
#print axioms VerifiedLcalc.EllipticCurve.centralFiniteBounds_correct
#print axioms VerifiedLcalc.EllipticCurve.squareTailRatio_correct
#print axioms VerifiedLcalc.EllipticCurve.squareTailBound_correct
#print axioms VerifiedLcalc.EllipticCurve.square_geometric_majorant
#print axioms VerifiedLcalc.EllipticCurve.central_tail_error
#print axioms VerifiedLcalc.EllipticCurve.evaluateCentral_correct
#print axioms VerifiedLcalc.EllipticCurve.centralPayload_sound
#print axioms VerifiedLcalc.EllipticCurve.evaluateCentral_sound
#print axioms VerifiedLcalc.EllipticCurve.analyticOrder_zero_of_central
#print axioms VerifiedLcalc.EllipticCurve.Examples.curve11_coefficient_prefix
#print axioms VerifiedLcalc.Certificates.Central_11_a2_M8_P53_plus.payload_correct
#print axioms VerifiedLcalc.Certificates.Central_11_a2_M8_P53_plus.encloses

-- The optional modularity assumption must not leak into the numerical core.
/-- info: 'VerifiedLcalc.EllipticCurve.centralPayload_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.EllipticCurve.centralPayload_sound

#print axioms VerifiedLcalc.EllipticCurve.coefficientFromFactors_model_eq_euler
#print axioms VerifiedLcalc.EllipticCurve.model_eulerCoefficient_abs_le_cube
#print axioms VerifiedLcalc.Numerics.mellin_one_split

/-- info: 'VerifiedLcalc.Numerics.mellin_one_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.Numerics.mellin_one_split

/--
info: 'VerifiedLcalc.EllipticCurve.model_eulerCoefficient_abs_le_cube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.EllipticCurve.model_eulerCoefficient_abs_le_cube

-- Additive arithmetic must remain independent of the modularity axiom.

/-- info: 'VerifiedLcalc.EllipticCurve.minimal_localPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.minimal_localPolynomial

/-- info: 'VerifiedLcalc.EllipticCurve.integral_c4_two_adic_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.integral_c4_two_adic_gap

/-- info: 'VerifiedLcalc.EllipticCurve.isMinimal_of_two_adic_c4_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.isMinimal_of_two_adic_c4_six

/-- info: 'VerifiedLcalc.EllipticCurve.minimal_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.minimal_of_witness

/-- info: 'VerifiedLcalc.EllipticCurve.additive_localPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.additive_localPolynomial

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a2.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a2.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a3.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a3.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C20_a4.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a2.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a2.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a3.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a3.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a4.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a5.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a5.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a6.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C24_a6.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a2.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a2.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a3.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a3.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C27_a4.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a2.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a2.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a3.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a3.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C32_a4.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a2.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a2.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a3.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a3.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C36_a4.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a2.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a2.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a3.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a3.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a4.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExamples.C40_a4.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.ReductionExamples.curve32_coefficient_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.ReductionExamples.curve32_coefficient_four

/-- info: 'VerifiedLcalc.EllipticCurve.twoAdicC4MinimalAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.twoAdicC4MinimalAt_correct

-- Broader arithmetic is independent of the opt-in modularity axiom.
/-- info: 'VerifiedLcalc.EllipticCurve.reduction_eq_variableChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.reduction_eq_variableChange

/-- info: 'VerifiedLcalc.EllipticCurve.semistable_localPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.semistable_localPolynomial

/-- info: 'VerifiedLcalc.EllipticCurve.semistable_primePower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.semistable_primePower

/-- info: 'VerifiedLcalc.EllipticCurve.semistable_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.semistable_prefix

/-- info: 'VerifiedLcalc.EllipticCurve.ArithmeticExamples.curve14_coefficient_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.ArithmeticExamples.curve14_coefficient_four

/-- info: 'VerifiedLcalc.EllipticCurve.ArithmeticExamples.curve17_coefficient_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.ArithmeticExamples.curve17_coefficient_four

-- This audit is opt-in. Its named modularity axiom is an expected dependency.
-- The default Audit.lean and default certificate modules do not import it.
#print axioms VerifiedLcalc.Assumptions.ellipticModularity
#print axioms VerifiedLcalc.Assumptions.ModularRealization.formL_differentiable
#print axioms VerifiedLcalc.Assumptions.ModularRealization.formL_hasSum
#print axioms VerifiedLcalc.Assumptions.ModularRealization.formL_eq_curveLSeries
#print axioms VerifiedLcalc.Assumptions.modularWitness_normalized
#print axioms VerifiedLcalc.Assumptions.modularWitness_goodPrime
#print axioms VerifiedLcalc.Assumptions.modularWitness_formL_differentiable
#print axioms VerifiedLcalc.Assumptions.modularWitness_formL_hasSum
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.continuedL_entire
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.continuedL_matches_euler_series
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.continuedL_agrees_with_curveLSeries
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.form_coefficient_two

#print axioms VerifiedLcalc.Assumptions.check_assumed_exact_sound
#print axioms VerifiedLcalc.Assumptions.check_assumed_numerical_sound
#print axioms VerifiedLcalc.Assumptions.check_assumed_numerical_lowerBound

-- Fail if the general implication acquires the custom axiom, or if the
-- assumption-dependent continuation acquires any additional custom axiom.
/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.formL_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.formL_hasSum

/--
info: 'VerifiedLcalc.Certificates.AssumedCurve11.continuedL_matches_euler_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.continuedL_matches_euler_series

#print axioms VerifiedLcalc.Assumptions.ModularRealization.central_upper_mellin
#print axioms VerifiedLcalc.Assumptions.ModularRealization.central_zero_of_negative_sign
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.arithmetic_level
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.arithmetic_sign
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.realization_level
#print axioms VerifiedLcalc.Certificates.AssumedCurve11.continuedL_central_integral
#print axioms VerifiedLcalc.Certificates.AssumedCurve37.arithmetic_sign
#print axioms VerifiedLcalc.Certificates.AssumedCurve37.central_vanishing
#print axioms VerifiedLcalc.Certificates.AssumedCurve37.analytic_rank_at_least_one

/--
info: 'VerifiedLcalc.Assumptions.ModularRealization.central_upper_mellin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.central_upper_mellin

/--
info: 'VerifiedLcalc.Certificates.AssumedCurve37.analytic_rank_at_least_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Certificates.AssumedCurve37.analytic_rank_at_least_one

#print axioms VerifiedLcalc.Certificates.AssumedCurve11Central.actual_prefix
#print axioms VerifiedLcalc.Certificates.AssumedCurve11Central.analytic_rank_zero
#print axioms VerifiedLcalc.Certificates.AssumedCurve11Central.certifiedRank_correct
#print axioms VerifiedLcalc.Assumptions.conditionalCertifiedBackend_sound

/--
info: 'VerifiedLcalc.Certificates.AssumedCurve11Central.analytic_rank_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Certificates.AssumedCurve11Central.analytic_rank_zero

/--
info: 'VerifiedLcalc.Assumptions.conditionalCertifiedBackend_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.conditionalCertifiedBackend_sound

/-- info: 'VerifiedLcalc.Assumptions.certifySemistableCentral' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifySemistableCentral

/-- info: 'VerifiedLcalc.Assumptions.generatedCertificateKeys_sound' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.generatedCertificateKeys_sound

/-- info: 'VerifiedLcalc.Assumptions.certifySemistableCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifySemistableCentralModel

/-- info: 'VerifiedLcalc.Assumptions.certifyMinimalCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifyMinimalCentralModel

/-- info: 'VerifiedLcalc.Assumptions.rank_lower_bound_of_semistable_negative' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.rank_lower_bound_of_semistable_negative

/-- info: 'VerifiedLcalc.Numerics.intervalMul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Numerics.intervalMul_sound

/-- info: 'VerifiedLcalc.Numerics.logBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Numerics.logBounds_sound

/-- info: 'VerifiedLcalc.Numerics.derivativeCellBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Numerics.derivativeCellBounds_sound

/-- info: 'VerifiedLcalc.Numerics.derivative_tail_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Numerics.derivative_tail_error

/-- info: 'VerifiedLcalc.Numerics.derivativeFiniteBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Numerics.derivativeFiniteBounds_sound

/-- info: 'VerifiedLcalc.EllipticCurve.derivativePayload_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.derivativePayload_contains

/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.mellin_first_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.mellin_first_derivative

/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.deriv_one_re_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.deriv_one_re_integral

/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.realDerivativeBounds_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.realDerivativeBounds_contains

/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.analyticOrder_one_of_derivativePayload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.analyticOrder_one_of_derivativePayload

/-- info: 'VerifiedLcalc.Assumptions.certifyDerivativeModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifyDerivativeModel

/-- info: 'VerifiedLcalc.Assumptions.generatedRankOneKeys_sound' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.generatedRankOneKeys_sound

/-- info: 'VerifiedLcalc.Certificates.DerivativeBatch.C37_a1.analytic_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certificates.DerivativeBatch.C37_a1.analytic_rank_one


/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples.C100_a1.coefficients_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples.C100_a1.coefficients_correct

/-- info: 'VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples.C100_a1.additive_factor_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples.C100_a1.additive_factor_5

/-- info: 'VerifiedLcalc.EllipticCurve.singularTrace_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.singularTrace_correct

/-- info: 'VerifiedLcalc.EllipticCurve.BadPrimeExamples.curve389_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.BadPrimeExamples.curve389_trace

/-- info: 'VerifiedLcalc.EllipticCurve.BadPrimeExamples.curve5077_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.BadPrimeExamples.curve5077_trace

/-- info: 'VerifiedLcalc.EllipticCurve.invariantMinimalAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.invariantMinimalAt_correct

/-- info: 'VerifiedLcalc.Assumptions.semistableSign_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.semistableSign_eq_fast

/-- info: 'VerifiedLcalc.Lmfdb.has_1100_cases' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Lmfdb.has_1100_cases

/-- info: 'VerifiedLcalc.Lmfdb.all_labels_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Lmfdb.all_labels_nodup


/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.formL_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.formL_eq

/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.analyticOrder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.analyticOrder_eq

/-- info: 'VerifiedLcalc.Assumptions.certifyCentralWithRealization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifyCentralWithRealization

/-- info: 'VerifiedLcalc.Assumptions.certifyGeneralMinimalCentral' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifyGeneralMinimalCentral

/-- info: 'VerifiedLcalc.Certificates.GeneralModularityExamples.additive_modularity' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certificates.GeneralModularityExamples.additive_modularity

/-- info: 'VerifiedLcalc.Certificates.GeneralModularityExamples.curve11_via_general_interface' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certificates.GeneralModularityExamples.curve11_via_general_interface

/-- info: 'VerifiedLcalc.Certificates.GeneralModularityExamples.curve37_via_general_interface' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certificates.GeneralModularityExamples.curve37_via_general_interface

-- These implications accept mathematical witnesses as arguments. They must
-- not depend on ellipticModularity, sorryAx, or native reduction axioms.

/-- info: 'WeierstrassCurve.localPolynomial_eq_of_not_hasGoodReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WeierstrassCurve.localPolynomial_eq_of_not_hasGoodReduction

/-- info: 'WeierstrassCurve.isMultiplicative_LFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WeierstrassCurve.isMultiplicative_LFunction

/-- info: 'VerifiedLcalc.EllipticCurve.localEulerFactor_apply_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.EllipticCurve.localEulerFactor_apply_pow_eq

/-- info: 'VerifiedLcalc.EllipticCurve.curveCoefficient_abs_le_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.EllipticCurve.curveCoefficient_abs_le_cube

/-- info: 'VerifiedLcalc.Numerics.hasSum_integral_exponential_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.Numerics.hasSum_integral_exponential_series

/--
info: 'VerifiedLcalc.Assumptions.ModularRealization.imaginaryFunction_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.imaginaryFunction_hasSum

/--
info: 'VerifiedLcalc.Assumptions.ModularRealization.central_exponential_hasSum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.central_exponential_hasSum

/--
info: 'VerifiedLcalc.Assumptions.ModularRealization.evaluateCentral_contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.evaluateCentral_contains

/--
info: 'VerifiedLcalc.Assumptions.ModularRealization.analyticOrder_zero_of_centralPayload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.analyticOrder_zero_of_centralPayload

/-- info: 'VerifiedLcalc.EulerProduct.apply_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.EulerProduct.apply_prime_pow

/-- info: 'VerifiedLcalc.RationalPrimes.norm_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.RationalPrimes.norm_injective

/-- info: 'VerifiedLcalc.EllipticCurve.LFunction_apply_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.EllipticCurve.LFunction_apply_prime_pow

/-- info: 'VerifiedLcalc.EllipticCurve.LFunction_abs_le_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.EllipticCurve.LFunction_abs_le_cube

/-- info: 'VerifiedLcalc.Assumptions.ModularRealization.prefix_of_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.ModularRealization.prefix_of_supported
open VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
set_option pp.fullNames true
/-- info: 'VerifiedLcalc.EllipticCurve.isSquareMod_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isSquareMod_correct
/-- info: 'VerifiedLcalc.EllipticCurve.tameAdditiveRoot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tameAdditiveRoot_correct
/-- info: 'VerifiedLcalc.EllipticCurve.localConductorRoot?_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localConductorRoot?_correct
/-- info: 'VerifiedLcalc.EllipticCurve.tameLevel_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tameLevel_eq_fast
/-- info: 'VerifiedLcalc.EllipticCurve.tameSign_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tameSign_eq_fast
/-- info: 'VerifiedLcalc.Assumptions.certifyTameCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms certifyTameCentralModel
/-- info: 'VerifiedLcalc.Assumptions.rank_lower_bound_of_tame_negative' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_lower_bound_of_tame_negative

/-- info: 'VerifiedLcalc.EllipticCurve.tateWitness?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.tateWitness?_sound

/-- info: 'VerifiedLcalc.EllipticCurve.translateIntegral_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.translateIntegral_correct

/-- info: 'VerifiedLcalc.EllipticCurve.translateIntegral_discriminant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.translateIntegral_discriminant

/-- info: 'VerifiedLcalc.EllipticCurve.cubicRepeated_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.cubicRepeated_correct

/-- info: 'VerifiedLcalc.EllipticCurve.twoCharacter_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.twoCharacter_correct

/-- info: 'VerifiedLcalc.EllipticCurve.tateWitness_valid_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.tateWitness_valid_correct

/-- info: 'VerifiedLcalc.EllipticCurve.wildRoot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.wildRoot_correct

/-- info: 'VerifiedLcalc.EllipticCurve.wildLevel_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.wildLevel_eq_fast

/-- info: 'VerifiedLcalc.EllipticCurve.wildSign_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.wildSign_eq_fast

/-- info: 'VerifiedLcalc.Assumptions.certifyWildCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.certifyWildCentralModel

/-- info: 'VerifiedLcalc.Assumptions.rank_lower_bound_of_wild_negative' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Assumptions.rank_lower_bound_of_wild_negative

/-- info: 'VerifiedLcalc.EllipticCurve.WildExpandedExamples.C27_a1.sign_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.WildExpandedExamples.C27_a1.sign_formula

/-- info: 'VerifiedLcalc.Certificates.Batch.C27_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certificates.Batch.C27_a1.analytic_rank_zero
