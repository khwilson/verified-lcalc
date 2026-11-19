import VerifiedLcalc.Assumptions.TameCertification
import VerifiedLcalc.Assumptions.TameNegativeSign
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
