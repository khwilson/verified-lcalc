import VerifiedLcalcTests.Arithmetic.BadPrimeExamples
import VerifiedLcalc.EllipticCurve.Tate.InvariantMinimality
import VerifiedLcalcTests.Arithmetic.LmfdbSupplementProofs
import VerifiedLcalc.EllipticCurve.Modularity.FastSign

/-! # Extended curve arithmetic axiom dependencies -/

-- This audit intentionally uses `#print axioms` to check proof dependencies.
set_option linter.hashCommand false

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

/-- info: 'VerifiedLcalc.Modularity.semistableSign_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Modularity.semistableSign_eq_fast

/-- info: 'VerifiedLcalc.Lmfdb.has_1100_cases' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Lmfdb.has_1100_cases

/-- info: 'VerifiedLcalc.Lmfdb.all_labels_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VerifiedLcalc.Lmfdb.all_labels_nodup
