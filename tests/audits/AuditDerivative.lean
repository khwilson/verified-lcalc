import VerifiedLcalc.Verification.DerivativeCertification

/-! # First derivative certificate axiom dependencies -/

-- This audit intentionally uses `#print axioms` to check proof dependencies.
set_option linter.hashCommand false

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

/-- info: 'VerifiedLcalc.Modularity.ModularRealization.mellin_first_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Modularity.ModularRealization.mellin_first_derivative

/-- info: 'VerifiedLcalc.Modularity.ModularRealization.deriv_one_re_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Modularity.ModularRealization.deriv_one_re_integral

/-- info: 'VerifiedLcalc.Modularity.ModularRealization.realDerivativeBounds_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Modularity.ModularRealization.realDerivativeBounds_contains

/-- info: 'VerifiedLcalc.Modularity.ModularRealization.analyticOrder_one_of_derivativePayload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Modularity.ModularRealization.analyticOrder_one_of_derivativePayload

/-- info: 'VerifiedLcalc.Certification.certifyDerivativeModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.certifyDerivativeModel
