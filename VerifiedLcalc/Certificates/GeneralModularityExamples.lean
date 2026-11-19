module

public import VerifiedLcalc.Assumptions.GeneralCertification
public import VerifiedLcalc.Certificates.Batch.C11_a2
public import VerifiedLcalc.Certificates.AssumedCurve37
public import VerifiedLcalc.EllipticCurve.SemistableArithmetic

@[expose] public section
namespace VerifiedLcalc.Certificates.GeneralModularityExamples
open EllipticCurve Assumptions

/-- This curve has additive reduction, so it is outside the semistable shortcut. -/
def additiveCurve : Artifacts.CurveEquation := ⟨0, 0, 0, 0, 1⟩

theorem additive_not_semistable : ¬ SemistableModel additiveCurve := by decide +kernel

theorem additive_modularity : Nonempty (ModularRealization additiveCurve) :=
  general_modularity additiveCurve (by decide +kernel)

/-- Any two supplied modular realizations agree even for an additive input. -/
theorem additive_continuation_independent (m n : ModularRealization additiveCurve) :
    m.formL = n.formL := m.formL_eq n

/-- Replay an existing complete numerical payload through the new general
interface. No semistability condition occurs in certifyGeneralMinimalCentral. -/
theorem curve11_via_general_interface :
    analyticOrderAt (modularWitness Batch.C11_a2.result.equation
      Batch.C11_a2.nonsingular).formL (1 : ℂ) = 0 := by
  let r := Batch.C11_a2.result
  have hs : SemistableModel r.equation := by decide +kernel
  let m := modularWitness r.equation Batch.C11_a2.nonsingular
  have hN : m.level = r.conductor :=
    (m.semistableLevel_eq hs).trans (by decide +kernel)
  have hw : m.rootNumber = r.rootNumber :=
    (m.semistableSign_eq hs).trans (by decide +kernel)
  apply certifyGeneralMinimalCentral r Batch.C11_a2.nonsingular
    (fun _ _ => semistable_isMinimal r.equation hs)
    ⟨m, hN, hw⟩ Batch.C11_a2.payload_correct
  decide +kernel

/-- A caller can use a different witness without comparing its level or sign
to the particular witness chosen for the cached certificate. -/
theorem curve11_any_realization (m : ModularRealization Batch.C11_a2.result.equation) :
    analyticOrderAt m.formL (1 : ℂ) = 0 := by
  rw [m.analyticOrder_eq (modularWitness _ Batch.C11_a2.nonsingular)]
  exact Batch.C11_a2.analytic_rank_zero

/-- Replay an existing exact lower bound through the unrestricted interface. -/
theorem curve37_via_general_interface :
    1 ≤ analyticOrderAt (modularWitness AssumedCurve37.equation
      AssumedCurve37.nonsingular).formL (1 : ℂ) :=
  certifyGeneralNegativeLowerBound AssumedCurve37.equation AssumedCurve37.nonsingular 37
    ⟨AssumedCurve37.realization, AssumedCurve37.realization_level, AssumedCurve37.realization_sign⟩

/-- Executable rank value carrying the proof from the general interface. -/
def certifiedRank : {n : ℕ //
    analyticOrderAt (modularWitness Batch.C11_a2.result.equation
      Batch.C11_a2.nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, curve11_via_general_interface⟩

/-- Executable lower bound; its type deliberately does not assert exact rank one. -/
def certifiedLowerBound : {n : ℕ // n ≤
    analyticOrderAt (modularWitness AssumedCurve37.equation
      AssumedCurve37.nonsingular).formL (1 : ℂ)} :=
  ⟨1, curve37_via_general_interface⟩

end VerifiedLcalc.Certificates.GeneralModularityExamples
