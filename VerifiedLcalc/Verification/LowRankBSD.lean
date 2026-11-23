/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Assumptions.LowRankBSD
public import VerifiedLcalc.Certificate.AnalyticFacts

/-!
# Opt-in rank-zero and rank-one consequences

These wrappers consume an exact analytic-rank fact for the same equation and
an explicit arithmetic modular realization. They are deliberately outside the
default certification imports.
-/

-- The rational ellipticity instance is derived locally from the explicit
-- nonsingularity proof, so `letI` is needed to elaborate `Module.finrank`.
set_option linter.style.haveILetI false

@[expose] public section

namespace VerifiedLcalc.Certification

/-- An exact analytic rank at most one gives the matching rational point rank,
under the isolated low-rank forward implication assumption. -/
theorem algebraic_finrank_of_conditional_analytic_rank
    {curve : WeierstrassCurve ℤ} (hn : curve.Δ ≠ 0)
    (fact : ConditionalAnalyticRank curve) (m : Modularity.ArithmeticModularRealization curve)
    (hsmall : fact.val ≤ 1) :
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = fact.val := by
  letI : (curve.baseChange ℚ).IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (curve.Δ : ℚ) ≠ 0 by exact_mod_cast hn)⟩
  exact Assumptions.analyticOrder_le_one_implies_finrank curve m fact.val hsmall
    (fact.correct m) hn

/-- A rank-zero analytic fact gives zero Mordell--Weil rank under the opt-in
forward implication assumption. -/
theorem algebraic_finrank_eq_zero_of_analytic_rank_zero
    {curve : WeierstrassCurve ℤ} (hn : curve.Δ ≠ 0)
    (fact : ConditionalAnalyticRank curve) (m : Modularity.ArithmeticModularRealization curve)
    (hzero : fact.val = 0) :
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = 0 := by
  calc
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = fact.val :=
      algebraic_finrank_of_conditional_analytic_rank hn fact m
        (by
          calc
            fact.val = 0 := hzero
            _ ≤ 1 := Nat.zero_le 1)
    _ = 0 := hzero

/-- A rank-one analytic fact gives rational point rank one under the opt-in
forward implication assumption. -/
theorem algebraic_finrank_eq_one_of_analytic_rank_one
    {curve : WeierstrassCurve ℤ} (hn : curve.Δ ≠ 0)
    (fact : ConditionalAnalyticRank curve) (m : Modularity.ArithmeticModularRealization curve)
    (hone : fact.val = 1) :
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = 1 := by
  calc
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = fact.val :=
      algebraic_finrank_of_conditional_analytic_rank hn fact m
        (by
          calc
            fact.val = 1 := hone
            _ ≤ 1 := Nat.le_refl 1)
    _ = 1 := hone

end VerifiedLcalc.Certification
