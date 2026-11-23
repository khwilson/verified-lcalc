/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.ArtifactData
public import VerifiedLcalc.Certificate.Analytic.EvidencePredicates
public import VerifiedLcalc.Certificate.Analytic.EnclosurePredicates
public import VerifiedLcalc.Certificate.Artifacts.ScanWitness
public import VerifiedLcalc.Certificate.Artifacts.Contracts
public import VerifiedLcalc.Certificate.Numerical.RankContracts
public import VerifiedLcalc.Certificate.Numerical.CentralFormula
public import VerifiedLcalc.Certificate.Numerical.Payloads
public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealizationData
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # L-values, derivatives and analytic rank

* `VerifiedLcalc.Certificate` certifies a finite scan of given boxes.
  `AnalyticCertificate` also proves the exact analytic order for the specified function
  and center. `SpecialLValueFacts` bounds the error in a reported Taylor leading coefficient
  for any arithmetic modular realization of the given curve.
* `EllipticCurve.CentralSeriesEvidence` gives the convergent split Mellin series, its finite
  sum, and a summand bound used to enclose the central value.
* `Artifacts.Checked` certifies the finite exact-rank artifact contract.
  `NumericalRanks.Checked` certifies the finite cutoff contract. `Artifacts.AnalyticEvidence`
  and `NumericalRanks.Evidence` supply the function, analyticity, and actual derivative
  enclosures for their respective artifacts.
* `CentralCurveEnclosure` and `DerivativeCurveEnclosure` bind the central and scaled
  first-derivative bounds to the real parts of the corresponding values for any explicit
  arithmetic modular realization. `CentralNumericalFact` and `DerivativeNumericalFact`
  retain finite payload checks, zero exclusion, and optional actual containment.
* `ConditionalAnalyticRank` gives the exact order at 1 for any explicit arithmetic modular
  realization. `CurvePrecisionFact` gives a checked derivative prefix within a cutoff for a
  fixed realization. `AnalyticFacts` collects optional payloads, rank, and special values.
-/

@[expose] public section

/-! ## Orders of vanishing and reported special values -/

namespace VerifiedLcalc

open EllipticCurve Modularity

/-- A proof-carrying finite rank contract. Its proof is entirely about the
supplied rectangles; the executable scan equation is exposed by compatibility. -/
structure Certificate (bs : List Box) where
  /-- First derivative index whose box excludes zero. -/
  rank : Nat
  /-- Finite mathematical witness for this rank and these boxes. -/
  sound : Witness bs rank

/-- An analytic order is certified by a finite witness on these exact boxes. -/
structure AnalyticCertificate (f : ℂ → ℂ) (center : ℂ) (bs : List Box) where
  /-- Claimed order of vanishing. -/
  rank : ℕ
  /-- The same boxes witness the first nonzero derivative at this rank. -/
  sound : Witness bs rank
  /-- The function has this analytic order at the specified center. -/
  correct : analyticOrderAt f center = rank

/-- A proved enclosure for the Taylor leading coefficient at the analytic
order of the actual curve L-function. -/
structure SpecialLValueFacts (curve : WeierstrassCurve ℤ) where
  /-- The order used to normalize the derivative by its factorial. -/
  order : Nat
  /-- The exact reported value and claimed error radius. -/
  claim : SpecialLValueClaim
  /-- The checked order and normalized leading coefficient bound for every
  arithmetic modular realization of this same curve. -/
  correct : ∀ m : ArithmeticModularRealization curve,
    analyticOrderAt m.formL 1 = order ∧
      |(iteratedDeriv order m.formL 1).re / (order.factorial : ℝ) -
        (claim.reported : ℝ)| ≤ (claim.error : ℝ)

end VerifiedLcalc

/-! ## Enclosures and numerical evidence -/

namespace VerifiedLcalc.EllipticCurve

/-- Remaining analytic obligations for an actual central value. The series
must be the convergent split-Mellin exponential series, not the raw Dirichlet
series evaluated outside its convergence domain. -/
structure CentralSeriesEvidence (r : CentralResult) (value : ℝ) where
  /-- Summands of the split Mellin series. -/
  series : Nat → ℝ
  /-- The summands converge to the actual value. -/
  formula : HasSum series value
  /-- The initial series sum is the exact finite Mellin expression. -/
  finiteSum : (∑ j ∈ Finset.range r.termLimit, series j) =
    centralFiniteValue r.coefficients r.rootNumber (2 * Real.pi / Real.sqrt r.conductor)
  /-- A quadratic-times-geometric majorant for every summand. -/
  majorant : ∀ j, |series j| ≤ ((1 + r.rootNumber : Int).natAbs : ℝ) *
    (((j + 1 : Nat) : ℝ) ^ 2 * (r.geometricUpper : ℝ) ^ (j + 1))

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.Artifacts

/-- A checked artifact retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical contract. -/
  artifact : Artifact
  /-- Proof that its request and boxes satisfy the expected contract. -/
  contract : WitnessAccepts expected artifact

end VerifiedLcalc.Artifacts

namespace VerifiedLcalc.NumericalRanks

/-- A checked numerical observation retains a proof of its pure contract. -/
structure Checked (expected : Request) where
  /-- Artifact that passed the mathematical acceptance conditions. -/
  artifact : Artifact
  /-- Proof that request, bound, and boxes satisfy the expected conditions. -/
  contract : CutoffAccepts expected artifact

end VerifiedLcalc.NumericalRanks

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

/-! ## Analytic certificate fields -/

namespace VerifiedLcalc

open EllipticCurve Modularity

/-- The central box encloses the real part of the actual central value. -/
structure CentralCurveEnclosure (curve : WeierstrassCurve ℤ) (r : CentralResult) : Type where
  /-- Containment for an explicit arithmetic realization. -/
  contains : ∀ m : ArithmeticModularRealization curve,
    r.box.Contains (Complex.ofReal (m.formL 1).re)

/-- The scaled first-derivative bounds enclose the actual raw derivative's real part. -/
structure DerivativeCurveEnclosure (curve : WeierstrassCurve ℤ) (r : DerivativeResult) : Type where
  /-- Containment after scaling the normalized integral enclosure. -/
  contains : ∀ m : ArithmeticModularRealization curve,
    r.realDerivativeBounds.Contains (deriv m.formL 1).re

/-- A central enclosure payload verified for this integral equation. -/
structure CentralNumericalFact (curve : WeierstrassCurve ℤ) where
  /-- The checked evaluator output. -/
  result : CentralResult
  /-- The output's equation is the subject of the fact. -/
  result_curve : result.equation = curve
  /-- The finite evaluator payload passes the mathematical checks. -/
  payload : CentralPayloadCorrect result
  /-- The enclosure excludes zero. -/
  excludes_zero : result.box.excludesZero = true
  /-- Actual scalar containment when arithmetic evidence is available. -/
  enclosure : Option (CentralCurveEnclosure curve result) := none

/-- A first-derivative enclosure payload verified for this integral equation. -/
structure DerivativeNumericalFact (curve : WeierstrassCurve ℤ) where
  /-- The checked evaluator output. -/
  result : DerivativeResult
  /-- The output's equation is the subject of the fact. -/
  result_curve : result.equation = curve
  /-- The finite evaluator payload passes the mathematical checks. -/
  payload : DerivativePayloadCorrect result
  /-- The enclosure excludes zero. -/
  excludes_zero : result.box.excludesZero = true
  /-- Actual scalar containment when arithmetic evidence is available. -/
  enclosure : Option (DerivativeCurveEnclosure curve result) := none

/-- An analytic rank that can be instantiated with any arithmetic realization. -/
structure ConditionalAnalyticRank (curve : WeierstrassCurve ℤ) where
  /-- The checked rank. -/
  val : Nat
  /-- The rank identification given an explicit arithmetic realization. -/
  correct : ∀ m : ArithmeticModularRealization curve, analyticOrderAt m.formL (1 : ℂ) = val

/-- Package a checked derivative prefix with its curve and supplied realization. -/
structure CurvePrecisionFact (curve : WeierstrassCurve ℤ) (m : ModularRealization curve) where
  /-- The curve, cutoff policy, derivative count and proposed gap. -/
  claim : Assumptions.CurvePrecisionClaim
  /-- The claim concerns the same curve as the realization. -/
  claim_curve : claim.equation = curve
  /-- The checked derivatives satisfy the claim's numerical cutoff. -/
  small : NumericalRanks.SmallDerivatives m.formL 1 claim.derivativeCount claim.policy.cutoff

/-- Optional verified numerical and analytic results attached to the same equation. -/
structure AnalyticFacts (curve : WeierstrassCurve ℤ) where
  /-- A central payload, including when it only supports the finite numerical check. -/
  central : Option (CentralNumericalFact curve) := none
  /-- A first-derivative payload, including when it only supports the finite numerical check. -/
  derivative : Option (DerivativeNumericalFact curve) := none
  /-- A rank result available only with checked arithmetic witnesses and an explicit realization. -/
  rank : Option (ConditionalAnalyticRank curve) := none
  /-- A reported Taylor leading coefficient checked against the actual enclosure. -/
  specialValue : Option (SpecialLValueFacts curve) := none

end VerifiedLcalc
