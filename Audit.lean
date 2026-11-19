import VerifiedLcalc.EllipticCurve.Bounds
import VerifiedLcalc.Numerics.MellinSplit
import VerifiedLcalcTests.Arithmetic.CentralExamples
import VerifiedLcalcTests.Fixtures.Curve11Central
import VerifiedLcalcTests.Fixtures.NumericalQuartic
import VerifiedLcalcTests.Arithmetic.Monomial
import VerifiedLcalcTests.Arithmetic.Numerics
import VerifiedLcalc.Lmfdb
import VerifiedLcalcTests.Fixtures.Cubic
import VerifiedLcalcTests.Fixtures.Curve11Arithmetic

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
#print axioms VerifiedLcalcTests.Fixtures.Cubic.certified_analytic_order


#print axioms VerifiedLcalc.EllipticCurve.weierstrass_correct
#print axioms VerifiedLcalc.EllipticCurve.residual_correct
#print axioms VerifiedLcalc.EllipticCurve.onCurve_correct
#print axioms VerifiedLcalc.EllipticCurve.onCurve_equation
#print axioms VerifiedLcalc.EllipticCurve.affinePoints_correct
#print axioms VerifiedLcalc.EllipticCurve.affinePoints_nodup
#print axioms VerifiedLcalc.EllipticCurve.affineCount_correct
#print axioms VerifiedLcalc.EllipticCurve.computePointCount_correct
#print axioms VerifiedLcalc.EllipticCurve.frobeniusTrace_correct
#print axioms VerifiedLcalc.EllipticCurve.isPrime_correct
#print axioms VerifiedLcalc.EllipticCurve.goodReduction_correct
#print axioms VerifiedLcalc.EllipticCurve.analysePrime_correct
#print axioms VerifiedLcalc.EllipticCurve.analysePrime_sound
#print axioms VerifiedLcalc.EllipticCurve.computePointCount_eq_card_point
#print axioms VerifiedLcalc.EllipticCurve.localPair_correct
#print axioms VerifiedLcalc.EllipticCurve.localCoefficient_correct
#print axioms VerifiedLcalc.EllipticCurve.localCoefficient_unique
#print axioms VerifiedLcalc.EllipticCurve.localSeries_correct
#print axioms VerifiedLcalc.EllipticCurve.localSeries_inverse
#print axioms VerifiedLcalcTests.Fixtures.Curve11Arithmetic.point_count_two
#print axioms VerifiedLcalcTests.Fixtures.Curve11Arithmetic.trace_two
#print axioms VerifiedLcalcTests.Fixtures.Curve11Arithmetic.euler_factor_two
#print axioms VerifiedLcalc.Numerics.rational_bound
#print axioms VerifiedLcalc.Numerics.square_bound

#print axioms Inclusion.IntervalDyadicReal.expBounds_bounds
#print axioms Inclusion.IntervalDyadicReal.exp_mem
#print axioms VerifiedLcalc.Numerics.exp_one_enclosure
#print axioms VerifiedLcalc.Numerics.exp_neg_one_enclosure
#print axioms VerifiedLcalc.Numerics.exp_negative_interval

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
#print axioms VerifiedLcalcTests.Fixtures.NumericalQuartic.checked
#print axioms VerifiedLcalcTests.Fixtures.NumericalQuartic.certified_small_derivatives
#print axioms VerifiedLcalcTests.Fixtures.NumericalQuartic.conditional_analytic_lower_bound
#print axioms VerifiedLcalcTests.Fixtures.NumericalQuartic.small_does_not_imply_rank_four

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
#print axioms VerifiedLcalcTests.Fixtures.Central_11_a2_M8_P53_plus.payload_correct
#print axioms VerifiedLcalcTests.Fixtures.Central_11_a2_M8_P53_plus.encloses

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
