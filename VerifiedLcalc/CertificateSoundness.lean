module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.Analytic
public import VerifiedLcalc.Certificates.AnalyticEvidence

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- The checker plus proved analytic evidence certifies the actual order of the
specified subject. No numerical producer is re-executed in this theorem. -/
theorem check_sound {expected : Request} {artifact : Artifact}
    (evidence : AnalyticEvidence expected artifact)
    (h : check expected artifact = true) :
    analyticOrderAt evidence.function (expected.subject.center : ℂ) = artifact.rank := by
  have hc := (check_correct _ _).mp h
  exact scan_analyticOrderAt evidence.analytic evidence.enclosures
    (witness_scan hc.2.2.2.2)

/-- In the currently supported interpretation, acceptance yields the concrete
monomial's analytic order, rather than the order of an arbitrarily chosen f. -/
theorem check_monomial_sound {expected : Request} {artifact : Artifact} {n : Nat}
    (hsubject : expected.subject = .monomial n)
    (evidence : AnalyticEvidence expected artifact)
    (h : check expected artifact = true) :
    analyticOrderAt (fun z : ℂ => z ^ n) 0 = artifact.rank := by
  have hf := evidence.denotes
  rw [hsubject] at hf
  change evidence.function = (fun z : ℂ => z ^ n) at hf
  simpa [hsubject, Subject.center, hf] using check_sound evidence h

end VerifiedLcalc.Artifacts
