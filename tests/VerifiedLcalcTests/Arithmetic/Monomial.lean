module

public import VerifiedLcalc.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import VerifiedLcalc.Demo
public import VerifiedLcalc.CertificateDemo
public import VerifiedLcalc.CertificateSoundness

@[expose] public section

namespace VerifiedLcalc.Examples

theorem cubic_analytic : AnalyticAt ℂ (fun z : ℂ => z ^ 3) 0 := by
  fun_prop

theorem cubic_enclosures :
    Encloses cubicBoxes (fun k => iteratedDeriv k (fun z : ℂ => z ^ 3) 0) := by
  norm_num [cubicBoxes, Encloses, Box.Contains, Set.mem_Icc, iteratedDeriv_fun_pow_zero]

/-- End-to-end theorem about a genuine complex analytic function. -/
theorem cubic_rank : analyticOrderAt (fun z : ℂ => z ^ 3) 0 = 3 :=
  scan_analyticOrderAt cubic_analytic cubic_enclosures cubicBoxes_computes

/-- The same search used at runtime, carrying its analytic correctness proof. -/
def cubicResult : Option (AnalyticCertificate (fun z : ℂ => z ^ 3) 0 cubicBoxes) :=
  computeRank _ _ cubicBoxes cubic_analytic cubic_enclosures

theorem cubicResult_correct : cubicResult.map (fun c => c.rank) = some 3 := by
  decide

/-- Analytic evidence for this exact subject and finite payload. -/
def cubicEvidence : Artifacts.AnalyticEvidence cubicRequest cubicArtifact :=
  { function := fun z : ℂ => z ^ 3
    denotes := rfl
    analytic := by simpa [cubicRequest, Artifacts.Subject.center] using cubic_analytic
    enclosures := by
      simpa [cubicArtifact, cubicRequest, Artifacts.Subject.center] using cubic_enclosures }

theorem cubicArtifact_rank : analyticOrderAt (fun z : ℂ => z ^ 3) 0 = cubicArtifact.rank :=
  Artifacts.check_monomial_sound rfl cubicEvidence cubicArtifact_checks

/-- A header and plausible boxes cannot bypass an unsupported interpretation. -/
theorem firstCurve_no_evidence (artifact : Artifacts.Artifact) :
    ¬ Nonempty (Artifacts.AnalyticEvidence firstCurveRequest artifact) := by
  rintro ⟨evidence⟩
  exact evidence.denotes

end VerifiedLcalc.Examples
