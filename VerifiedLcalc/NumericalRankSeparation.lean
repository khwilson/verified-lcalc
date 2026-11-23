/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.NumericalRankSoundness
public import VerifiedLcalc.Certificate.Analytic.EvidencePredicates

/-! Conditional separation theorems for exact analytic rank bounds. -/

@[expose] public section

namespace VerifiedLcalc.NumericalRanks

/-- The strict margin matters: an enclosure may include its cutoff endpoints. -/
theorem exactVanishing_of_gap {f : ℂ → ℂ} {center : ℂ} {n : Nat} {eps gap : Rat}
    (separated : NonzeroDerivativeGap f center n gap) (margin : eps < gap) :
    ExactVanishingHypothesis f center n eps := by
  intro k hk small
  by_contra hn
  have hm : (eps : ℝ) < (gap : ℝ) := by exact_mod_cast margin
  rcases separated k hk hn with hre | him
  · exact (not_le_of_gt hm) (hre.trans small.1)
  · exact (not_le_of_gt hm) (him.trans small.2)

/-- Smallness plus an explicit separation assumption gives a genuine, conditional
analytic-order lower bound. No separation principle is installed as an axiom. -/
theorem lowerBound_of_small_gap {f : ℂ → ℂ} {center : ℂ} {n : Nat} {eps gap : Rat}
    (analytic : AnalyticAt ℂ f center) (small : SmallDerivatives f center n eps)
    (separated : NonzeroDerivativeGap f center n gap) (margin : eps < gap) :
    (n : ℕ∞) ≤ analyticOrderAt f center := by
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero analytic).mpr
  intro k hk
  exact exactVanishing_of_gap separated margin k hk (small k hk)

/-- Exact rank also needs nonvanishing of the next derivative. A lower-bound
observation alone is insufficient even after adding separation. -/
theorem rank_eq_of_small_gap {f : ℂ → ℂ} {center : ℂ} {n : Nat} {eps gap : Rat}
    (analytic : AnalyticAt ℂ f center) (small : SmallDerivatives f center n eps)
    (separated : NonzeroDerivativeGap f center n gap) (margin : eps < gap)
    (next_nonzero : iteratedDeriv n f center ≠ 0) :
    analyticOrderAt f center = n := by
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero analytic).mpr
  exact ⟨fun k hk => exactVanishing_of_gap separated margin k hk (small k hk), next_nonzero⟩

end VerifiedLcalc.NumericalRanks
