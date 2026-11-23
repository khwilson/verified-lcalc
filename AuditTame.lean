import VerifiedLcalc.Verification.TameCertification
import VerifiedLcalc.Verification.TameNegativeSign
open VerifiedLcalc.EllipticCurve VerifiedLcalc.Modularity VerifiedLcalc.Certification
set_option linter.hashCommand false
set_option linter.style.setOption false
set_option pp.fullNames true
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
/-- info: 'VerifiedLcalc.Certification.certifyTameCentralModel' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms certifyTameCentralModel
/-- info: 'VerifiedLcalc.Certification.rank_lower_bound_of_tame_negative' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_lower_bound_of_tame_negative
