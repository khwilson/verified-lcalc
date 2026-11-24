import VerifiedLcalcTests.Arithmetic.ArithmeticExamples

/-! # Elliptic curve arithmetic axiom dependencies -/

-- This audit intentionally uses `#print axioms` to check proof dependencies.
set_option linter.hashCommand false

-- Broader arithmetic is independent of the opt-in modularity axiom.
/-- info: 'WeierstrassCurve.reduction_eq_variableChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms WeierstrassCurve.reduction_eq_variableChange

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
