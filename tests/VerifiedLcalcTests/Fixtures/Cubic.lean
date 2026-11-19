module

public import VerifiedLcalcTests.Arithmetic.Monomial

@[expose] public section
open VerifiedLcalc

namespace VerifiedLcalcTests.Fixtures.Cubic

open VerifiedLcalc VerifiedLcalc.Examples

-- Polynomial demonstration; this is not an elliptic-curve certificate.
-- Only the supplied payload is checked; no numerical producer is run.
def artifact : Artifacts.Artifact :=
  { request := { formatVersion := 1,                subject := VerifiedLcalc.Artifacts.Subject.monomial 3,                settings := { precisionBits := 0, termLimit := 0, maxDerivative := 3 },                build := { leanToolchain := "leanprover/lean4:v4.36.0-rc2",                           mathlibRevision := "3440367ed1804626334f13a3a534a9cbb3385a59",                           producerRevision := "exact-polynomial-demo-v1",                           checkerRevision := "derivative-box-checker-v1" } },   rank := 3,   derivativeBoxes := [{ reLo := 0, reHi := 0, imLo := 0, imHi := 0 },                       { reLo := 0, reHi := 0, imLo := 0, imHi := 0 },                       { reLo := 0, reHi := 0, imLo := 0, imHi := 0 },                       { reLo := 6, reHi := 6, imLo := 0, imHi := 0 }] }

theorem checked : Artifacts.check cubicRequest artifact = true := by decide

theorem certified_computation : scan artifact.derivativeBoxes = some artifact.rank :=
  ((Artifacts.check_correct _ _).mp checked).2.2.2.2

def evidence : Artifacts.AnalyticEvidence cubicRequest artifact :=
  { function := fun z : ℂ => z ^ 3
    denotes := rfl
    analytic := by simpa [cubicRequest, Artifacts.Subject.center] using cubic_analytic
    enclosures := by
      have hboxes : artifact.derivativeBoxes = cubicBoxes := by decide
      rw [hboxes]
      simpa [cubicRequest, Artifacts.Subject.center] using cubic_enclosures }

theorem certified_analytic_order : analyticOrderAt (fun z : ℂ => z ^ 3) 0 = 3 :=
  Artifacts.check_monomial_sound rfl evidence checked

end VerifiedLcalcTests.Fixtures.Cubic
