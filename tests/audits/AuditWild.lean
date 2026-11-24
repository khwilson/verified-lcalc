import VerifiedLcalcTests.Arithmetic.WildExamples
import VerifiedLcalc.Verification.WildCertification

/-! # Wild reduction axiom dependencies -/

-- This audit intentionally uses `#print axioms` to check proof dependencies.
set_option linter.hashCommand false

/-- info: 'VerifiedLcalc.EllipticCurve.tateWitness?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.tateWitness?_sound



/-- info: 'VerifiedLcalc.EllipticCurve.cubicRepeated_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.EllipticCurve.cubicRepeated_correct


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

/-- info: 'VerifiedLcalc.Certification.certifyWildCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.certifyWildCentralModel

/-- info: 'VerifiedLcalc.Certification.rank_lower_bound_of_wild_negative' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Certification.rank_lower_bound_of_wild_negative
