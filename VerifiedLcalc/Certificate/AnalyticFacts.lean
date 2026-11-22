/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certification.GeneralCertification
public import VerifiedLcalc.Certification.DerivativeEvaluator
public import VerifiedLcalc.Certification.Precision
public import VerifiedLcalc.Certificates.SpecialValue

/-!
# Typed numerical and analytic evidence

A checked numerical payload records what the kernel verified about its exact
input. The associated rank fact requires an explicit arithmetic modular
realization, so storing it preserves the axiom boundary of finite projections.
-/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve Modularity Certification

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

/-- An explicit separation hypothesis upgrades the checked prefix to a lower bound. -/
theorem CurvePrecisionFact.lower_bound {curve : WeierstrassCurve ℤ}
    {m : ModularRealization curve} (fact : CurvePrecisionFact curve m)
    (gap : NumericalRanks.NonzeroDerivativeGap m.formL 1 fact.claim.derivativeCount
      fact.claim.nonzeroGap) (wide : fact.claim.policy.cutoff < fact.claim.nonzeroGap) :
    (fact.claim.derivativeCount : ℕ∞) ≤ analyticOrderAt m.formL 1 :=
  NumericalRanks.lowerBound_of_small_gap (m.formL_differentiable.analyticAt 1) fact.small gap wide

/-- Exact order also requires the next derivative to be nonzero. -/
theorem CurvePrecisionFact.exact_rank {curve : WeierstrassCurve ℤ}
    {m : ModularRealization curve} (fact : CurvePrecisionFact curve m)
    (gap : NumericalRanks.NonzeroDerivativeGap m.formL 1 fact.claim.derivativeCount
      fact.claim.nonzeroGap) (wide : fact.claim.policy.cutoff < fact.claim.nonzeroGap)
    (next : iteratedDeriv fact.claim.derivativeCount m.formL 1 ≠ 0) :
    analyticOrderAt m.formL 1 = fact.claim.derivativeCount :=
  NumericalRanks.rank_eq_of_small_gap (m.formL_differentiable.analyticAt 1) fact.small gap wide next

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

/-- The checked conductor and sign agree with any supplied arithmetic realization. -/
private theorem realization_matching {curve : WeierstrassCurve ℤ}
    (m : ArithmeticModularRealization curve) (hn : curve.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid curve)
    (d : WildData) (hd : d.Valid curve) {N : Nat} {w : Int}
    (hN : wildLevelFast curve d = N) (hw : wildSignFast curve d = w) :
    m.level = N ∧ m.rootNumber = w := by
  let : (curve.baseChange ℚ).IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (curve.Δ : ℚ) ≠ 0 by exact_mod_cast hn)⟩
  have hmin := globalMinimal_of_witness curve v hv
  exact ⟨(m.wildLevel_eq hmin d hd).trans ((wildLevel_eq_fast curve d).trans hN),
    (m.wildSign_eq hmin d hd).trans ((wildSign_eq_fast curve d hd).trans hw)⟩

/-- A central payload verifies order zero for any compatible arithmetic realization. -/
theorem CentralNumericalFact.rank_with_realization {curve : WeierstrassCurve ℤ}
    (fact : CentralNumericalFact curve) (hn : curve.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid curve) (d : WildData) (hd : d.Valid curve)
    (hN : wildLevelFast curve d = fact.result.conductor)
    (hw : wildSignFast curve d = fact.result.rootNumber) (m : ArithmeticModularRealization curve) :
    analyticOrderAt m.formL (1 : ℂ) = 0 := by
  rcases fact with ⟨r, hcurve, hp, hz, _⟩
  subst curve
  obtain ⟨hlevel, hsign⟩ := realization_matching m hn v hv d hd hN hw
  apply certifyCentralWithRealization r m.toModularRealization hlevel hsign hp _ hz
  rw [hp.2.2.1]
  exact minimal_prefix r.equation hn (minimal_of_witness r.equation v hv) r.termLimit

/-- A first-derivative payload verifies order one for any compatible realization. -/
theorem DerivativeNumericalFact.rank_with_realization {curve : WeierstrassCurve ℤ}
    (fact : DerivativeNumericalFact curve) (hn : curve.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid curve) (d : WildData) (hd : d.Valid curve)
    (hN : wildLevelFast curve d = fact.result.conductor)
    (hw : wildSignFast curve d = -1) (m : ArithmeticModularRealization curve) :
    analyticOrderAt m.formL (1 : ℂ) = 1 := by
  rcases fact with ⟨r, hcurve, hp, hz, _⟩
  subst curve
  obtain ⟨hlevel, hsign⟩ := realization_matching m hn v hv d hd hN hw
  apply m.toModularRealization.analyticOrder_one_of_derivativePayload r hp hlevel.symm hsign _ hz
  rw [hp.2.2.2.1]
  exact minimal_prefix r.equation hn (minimal_of_witness r.equation v hv) r.termLimit

/-- The checked central payload and arithmetic evidence yield a true central enclosure. -/
theorem CentralNumericalFact.contains_with_realization {curve : WeierstrassCurve ℤ}
    (fact : CentralNumericalFact curve) (hn : curve.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid curve) (d : WildData) (hd : d.Valid curve)
    (hN : wildLevelFast curve d = fact.result.conductor)
    (hw : wildSignFast curve d = fact.result.rootNumber) (m : ArithmeticModularRealization curve) :
    fact.result.box.Contains (Complex.ofReal (m.formL 1).re) := by
  rcases fact with ⟨r, hcurve, hp, _, _⟩
  subst curve
  obtain ⟨hlevel, hsign⟩ := realization_matching m hn v hv d hd hN hw
  apply centralPayload_sound hp
    (m.toModularRealization.centralSeriesEvidence_of_coefficients
      r hp rfl hlevel.symm hsign.symm _)
  rw [hp.2.2.1]
  exact minimal_prefix r.equation hn (minimal_of_witness r.equation v hv) r.termLimit

/-- The checked scaled interval encloses the first derivative for an actual realization. -/
theorem DerivativeNumericalFact.contains_with_realization {curve : WeierstrassCurve ℤ}
    (fact : DerivativeNumericalFact curve) (hn : curve.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid curve) (d : WildData) (hd : d.Valid curve)
    (hN : wildLevelFast curve d = fact.result.conductor)
    (hw : wildSignFast curve d = -1) (m : ArithmeticModularRealization curve) :
    fact.result.realDerivativeBounds.Contains (deriv m.formL 1).re := by
  rcases fact with ⟨r, hcurve, hp, _, _⟩
  subst curve
  obtain ⟨hlevel, hsign⟩ := realization_matching m hn v hv d hd hN hw
  apply m.toModularRealization.realDerivativeBounds_contains r hp hlevel.symm hsign
  rw [hp.2.2.2.1]
  exact minimal_prefix r.equation hn (minimal_of_witness r.equation v hv) r.termLimit

end VerifiedLcalc
