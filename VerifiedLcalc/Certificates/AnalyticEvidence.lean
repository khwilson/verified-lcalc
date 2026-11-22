module

public import VerifiedLcalc.Certificates.AnalyticRank
public import VerifiedLcalc.Certificates.NumericalRanks
public import Mathlib.Analysis.Analytic.Order

/-! Proof obligations relating supplied boxes to the mathematical function. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

/-- Supported mathematical interpretation. Elliptic subjects await an
independent theorem identifying their L-function. -/
def Subject.Denotes (subject : Subject) (f : ℂ → ℂ) : Prop :=
  match subject with
  | .monomial n => f = (fun z : ℂ => z ^ n)
  | .ellipticCurve _ _ => False

/-- Data checks alone cannot supply an elliptic-curve interpretation. -/
theorem ellipticCurve_not_denotes (e : (WeierstrassCurve ℤ))
    (n : Normalization) (f : ℂ → ℂ) :
    ¬ (Subject.ellipticCurve e n).Denotes f := by
  simp [Subject.Denotes]

/-- Proof obligations connecting a finite artifact to its intended function. -/
structure AnalyticEvidence (expected : Request) (artifact : Artifact) where
  /-- Function whose derivatives are enclosed. -/
  function : ℂ → ℂ
  /-- The request's subject denotes this function. -/
  denotes : expected.subject.Denotes function
  /-- The function is analytic at the documented center. -/
  analytic : AnalyticAt ℂ function (expected.subject.center : ℂ)
  /-- Each supplied box encloses the corresponding derivative. -/
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k function (expected.subject.center : ℂ))

end VerifiedLcalc.Artifacts

namespace VerifiedLcalc.NumericalRanks

/-- Coordinatewise bounds for the first `n` derivatives; this asserts
smallness only and does not claim exact vanishing. -/
def SmallDerivatives (f : ℂ → ℂ) (center : ℂ) (n : Nat) (eps : Rat) : Prop :=
  ∀ k < n, |(iteratedDeriv k f center).re| ≤ (eps : ℝ) ∧
    |(iteratedDeriv k f center).im| ≤ (eps : ℝ)

/-- The numerical request's subject, analyticity, and true-derivative boxes. -/
structure Evidence (expected : Request) (artifact : Artifact) where
  /-- Function whose derivatives are enclosed. -/
  function : ℂ → ℂ
  /-- The request's subject denotes this function. -/
  denotes : expected.computation.subject.Denotes function
  /-- The function is analytic at the documented center. -/
  analytic : AnalyticAt ℂ function (expected.computation.subject.center : ℂ)
  /-- Each supplied box encloses the corresponding derivative. -/
  enclosures : Encloses artifact.derivativeBoxes
    (fun k => iteratedDeriv k function (expected.computation.subject.center : ℂ))

/-- Extra hypothesis needed to turn small derivatives into exact zeros. -/
def ExactVanishingHypothesis (f : ℂ → ℂ) (center : ℂ) (n : Nat) (eps : Rat) : Prop :=
  ∀ k < n, (|(iteratedDeriv k f center).re| ≤ (eps : ℝ) ∧
    |(iteratedDeriv k f center).im| ≤ (eps : ℝ)) → iteratedDeriv k f center = 0

end VerifiedLcalc.NumericalRanks
