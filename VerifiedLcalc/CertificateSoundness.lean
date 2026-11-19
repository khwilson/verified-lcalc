module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.Analytic

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Supported mathematical interpretation. There is deliberately no elliptic
curve interpretation until the actual L-function and its normalization exist. -/
def Subject.Denotes (subject : Subject) (f : ℂ → ℂ) : Prop :=
  match subject with
  | .monomial n => f = (fun z : ℂ => z ^ n)
  | .ellipticCurve _ _ => False

/-- Data checks cannot invent the missing elliptic-curve mathematics. -/
theorem ellipticCurve_not_denotes (e : CurveEquation) (n : Normalization) (f : ℂ → ℂ) :
    ¬ (Subject.ellipticCurve e n).Denotes f := by
  simp [Subject.Denotes]

/-- Proof obligations connecting a finite artifact to the intended analytic
function. The expensive evaluator must establish these using its own correctness
and error-bound theorems. They cannot be replaced by database ranks. -/
structure AnalyticEvidence (expected : Request) (artifact : Artifact) where
  function : ℂ → ℂ
  denotes : expected.subject.Denotes function
  analytic : AnalyticAt ℂ function (expected.subject.center : ℂ)
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k function (expected.subject.center : ℂ))

/-- The checker plus proved analytic evidence certifies the actual order of the
specified subject. No numerical producer is re-executed in this theorem. -/
theorem check_sound {expected : Request} {artifact : Artifact}
    (evidence : AnalyticEvidence expected artifact)
    (h : check expected artifact = true) :
    analyticOrderAt evidence.function (expected.subject.center : ℂ) = artifact.rank := by
  have hc := (check_correct _ _).mp h
  exact scan_analyticOrderAt evidence.analytic evidence.enclosures hc.2.2.2.2

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
