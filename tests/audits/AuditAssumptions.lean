import VerifiedLcalc.Verification.CentralCertification
import VerifiedLcalcTests.Fixtures.AssumedCurve11Central
import VerifiedLcalc.Verification.NegativeSign
import VerifiedLcalcTests.Fixtures.AssumedCurve11
import VerifiedLcalc.Verification.NumericalCertification
import VerifiedLcalcTests.Fixtures.AssumedCurve37

set_option linter.hashCommand false

-- This audit is opt-in. Its named modularity axiom is an expected dependency.
-- The default Audit.lean and default certificate modules do not import it.
#print axioms VerifiedLcalc.Assumptions.ellipticModularity
#print axioms VerifiedLcalc.Modularity.ModularRealization.formL_differentiable
#print axioms VerifiedLcalc.Modularity.ModularRealization.formL_hasSum
#print axioms VerifiedLcalc.Modularity.ModularRealization.formL_eq_curveLSeries
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.continuedL_entire
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.continuedL_matches_euler_series
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.continuedL_agrees_with_curveLSeries
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.form_coefficient_two

#print axioms VerifiedLcalc.Certification.check_assumed_exact_sound
#print axioms VerifiedLcalc.Certification.check_assumed_numerical_sound
#print axioms VerifiedLcalc.Certification.check_assumed_numerical_lowerBound

-- Fail if the general implication acquires the custom axiom, or if the
-- assumption-dependent continuation acquires any additional custom axiom.
/-- info: 'VerifiedLcalc.Modularity.ModularRealization.formL_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VerifiedLcalc.Modularity.ModularRealization.formL_hasSum

/--
info: 'VerifiedLcalcTests.Fixtures.AssumedCurve11.continuedL_matches_euler_series' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.continuedL_matches_euler_series

#print axioms VerifiedLcalc.Modularity.ModularRealization.central_upper_mellin
#print axioms VerifiedLcalc.Modularity.ModularRealization.central_zero_of_negative_sign
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.arithmetic_level
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.arithmetic_sign
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.realization_level
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11.continuedL_central_integral
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve37.arithmetic_sign
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve37.central_vanishing
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve37.analytic_rank_at_least_one

/--
info: 'VerifiedLcalc.Modularity.ModularRealization.central_upper_mellin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VerifiedLcalc.Modularity.ModularRealization.central_upper_mellin

/--
info: 'VerifiedLcalcTests.Fixtures.AssumedCurve37.analytic_rank_at_least_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve37.analytic_rank_at_least_one

#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11Central.actual_prefix
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11Central.analytic_rank_zero
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11Central.certifiedRank_correct

/--
info: 'VerifiedLcalcTests.Fixtures.AssumedCurve11Central.analytic_rank_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 VerifiedLcalc.Assumptions.ellipticModularity]
-/
#guard_msgs in
#print axioms VerifiedLcalcTests.Fixtures.AssumedCurve11Central.analytic_rank_zero

/-- info: 'VerifiedLcalc.Certification.certifySemistableCentral' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.certifySemistableCentral

/-- info: 'VerifiedLcalc.Certification.certifySemistableCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.certifySemistableCentralModel

/-- info: 'VerifiedLcalc.Certification.certifyMinimalCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.certifyMinimalCentralModel

/-- info: 'VerifiedLcalc.Certification.rank_lower_bound_of_semistable_negative' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.rank_lower_bound_of_semistable_negative
