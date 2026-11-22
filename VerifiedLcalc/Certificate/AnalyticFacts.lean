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
public import VerifiedLcalc.Certificate.Witnesses.AnalyticFacts

/-!
# Typed numerical and analytic evidence

A checked numerical payload records what the kernel verified about its exact
input. The associated rank fact requires an explicit arithmetic modular
realization, so storing it preserves the axiom boundary of finite projections.
-/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve Modularity Certification

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
