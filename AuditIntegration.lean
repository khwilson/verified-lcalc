import VerifiedLcalc.Assumptions.Prefix
import VerifiedLcalc.Assumptions.CentralEvaluator

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
