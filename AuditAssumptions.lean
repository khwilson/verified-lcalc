import VerifiedLcalc.Assumptions.NegativeSign
import VerifiedLcalc.Assumptions.Regression
import VerifiedLcalc.Certificates.AssumedCurve11
import VerifiedLcalc.Assumptions.Certificates
import VerifiedLcalc.Certificates.AssumedCurve37

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
