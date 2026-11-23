/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Analytic.EvidencePredicates
public import VerifiedLcalc.Certificate.Analytic.EnclosurePredicates
public import VerifiedLcalc.Certificate.Witnesses.NumericalRankData

/-! Structures containing analytic obligations for supplied evidence. -/

@[expose] public section

namespace VerifiedLcalc.Artifacts

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

end VerifiedLcalc.NumericalRanks
