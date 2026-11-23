module

public import VerifiedLcalc.Verification.GeneralCertification
public import VerifiedLcalcTests.Fixtures.AssumedCurve37
public import VerifiedLcalc.EllipticCurve.SemistableArithmetic

/-! # General modularity and uniqueness of realizations for an additive curve -/

@[expose] public section
open VerifiedLcalc.Certification
open VerifiedLcalc
namespace VerifiedLcalcTests.Fixtures.GeneralModularityExamples
open EllipticCurve Modularity

/-- This curve has additive reduction, so it is outside the semistable shortcut. -/
def additiveCurve : WeierstrassCurve ℤ := ⟨0, 0, 0, 0, 1⟩

theorem additive_not_semistable : ¬ SemistableModel additiveCurve := by decide +kernel

theorem additive_modularity : Nonempty (ModularRealization additiveCurve) :=
  general_modularity additiveCurve (by decide +kernel)

/-- Any two supplied modular realizations agree even for an additive input. -/
theorem additive_continuation_independent (m n : ModularRealization additiveCurve) :
    m.formL = n.formL := m.formL_eq n

/-- Replay an existing exact lower bound through the unrestricted interface. -/
theorem curve37_via_general_interface :
    1 ≤ analyticOrderAt (modularWitness AssumedCurve37.equation
      AssumedCurve37.nonsingular).formL (1 : ℂ) :=
  certifyGeneralNegativeLowerBound AssumedCurve37.equation AssumedCurve37.nonsingular 37
    ⟨AssumedCurve37.realization, AssumedCurve37.realization_level, AssumedCurve37.realization_sign⟩

/-- Executable lower bound; its type deliberately does not assert exact rank one. -/
def certifiedLowerBound : {n : ℕ // n ≤
    analyticOrderAt (modularWitness AssumedCurve37.equation
      AssumedCurve37.nonsingular).formL (1 : ℂ)} :=
  ⟨1, curve37_via_general_interface⟩

end VerifiedLcalcTests.Fixtures.GeneralModularityExamples
