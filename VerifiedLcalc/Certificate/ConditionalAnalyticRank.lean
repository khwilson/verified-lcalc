/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certification.GeneralCertification
public import VerifiedLcalc.Certification.DerivativeEvaluator

/-! # Rank certificates for an explicit arithmetic modular realization -/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve Modularity Certification

/-- A checked analytic rank which can be instantiated with any arithmetic realization. -/
structure ConditionalAnalyticRank (curve : WeierstrassCurve ℤ) where
  /-- The rank checked against the independently certified analytic order. -/
  val : Nat
  /-- Rank identification given an explicit arithmetic realization of this equation. -/
  correct : ∀ m : ArithmeticModularRealization curve, analyticOrderAt m.formL (1 : ℂ) = val

/-- The checked conductor and sign agree with any supplied arithmetic realization. -/
theorem ConditionalAnalyticRank.realization_matching {curve : WeierstrassCurve ℤ}
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

/-- A checked central payload proves exact order zero under the supplied realization. -/
theorem ConditionalAnalyticRank.central (r : CentralResult) (hn : r.equation.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid r.equation) (d : WildData) (hd : d.Valid r.equation)
    (hN : wildLevelFast r.equation d = r.conductor)
    (hw : wildSignFast r.equation d = r.rootNumber)
    (hp : CentralPayloadCorrect r) (hz : r.box.excludesZero = true)
    (m : ArithmeticModularRealization r.equation) :
    analyticOrderAt m.formL (1 : ℂ) = 0 := by
  obtain ⟨hlevel, hsign⟩ := realization_matching m hn v hv d hd hN hw
  apply certifyCentralWithRealization r m.toModularRealization hlevel hsign hp _ hz
  rw [hp.2.2.1]
  exact minimal_prefix r.equation hn (minimal_of_witness r.equation v hv) r.termLimit

/-- A checked first-derivative payload proves exact order one under the supplied realization. -/
theorem ConditionalAnalyticRank.derivative (r : DerivativeResult) (hn : r.equation.Δ ≠ 0)
    (v : MinimalityWitness) (hv : v.Valid r.equation) (d : WildData) (hd : d.Valid r.equation)
    (hN : wildLevelFast r.equation d = r.conductor) (hw : wildSignFast r.equation d = -1)
    (hp : DerivativePayloadCorrect r) (hz : r.box.excludesZero = true)
    (m : ArithmeticModularRealization r.equation) :
    analyticOrderAt m.formL (1 : ℂ) = 1 := by
  obtain ⟨hlevel, hsign⟩ := realization_matching m hn v hv d hd hN hw
  apply m.toModularRealization.analyticOrder_one_of_derivativePayload r hp hlevel.symm hsign _ hz
  rw [hp.2.2.2.1]
  exact minimal_prefix r.equation hn (minimal_of_witness r.equation v hv) r.termLimit

end VerifiedLcalc
