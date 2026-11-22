/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalcTests.Arithmetic.Monomial

/-! End-to-end finite and analytic certificate for the cubic monomial. -/

@[expose] public section
open VerifiedLcalc

namespace VerifiedLcalcTests.Fixtures.Cubic

open VerifiedLcalc VerifiedLcalc.Examples

-- Polynomial demonstration; this is not an elliptic-curve certificate.
-- Only the supplied payload is checked; no numerical producer is run.
def artifact : Artifacts.Artifact :=
  { request := cubicRequest, rank := 3, derivativeBoxes := cubicBoxes }

theorem checked : Artifacts.check cubicRequest artifact = true := by decide

theorem certified_computation : scan artifact.derivativeBoxes = some artifact.rank :=
  ((Artifacts.check_correct _ _).mp checked).2.2.2.2

def evidence : Artifacts.AnalyticEvidence cubicRequest artifact :=
  { function := fun z : ℂ => z ^ 3
    denotes := rfl
    analytic := by simpa [cubicRequest, Artifacts.Subject.center] using cubic_analytic
    enclosures := by
      simpa [artifact, cubicRequest, Artifacts.Subject.center] using cubic_enclosures }

theorem certified_analytic_order : analyticOrderAt (fun z : ℂ => z ^ 3) 0 = 3 :=
  Artifacts.check_monomial_sound rfl evidence checked

end VerifiedLcalcTests.Fixtures.Cubic
