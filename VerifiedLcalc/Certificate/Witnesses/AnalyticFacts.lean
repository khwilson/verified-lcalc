/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Enclosures
public import VerifiedLcalc.Certificate.Witnesses.NumericalData
public import VerifiedLcalc.Certificate.Witnesses.SpecialValue
public import VerifiedLcalc.Certificates.NumericalContracts
public import VerifiedLcalc.Certificates.AnalyticEnclosures
public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealization
public import VerifiedLcalc.EllipticCurve.Modularity.Realization
public import VerifiedLcalc.Certificate.Witnesses.CurvePrecisionClaim
public import VerifiedLcalc.NumericalRankSeparation
public import VerifiedLcalc.Numerics.RealInterval
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Checked analytic fact structures -/

@[expose] public section

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
