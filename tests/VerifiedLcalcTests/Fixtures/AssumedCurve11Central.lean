module

public import VerifiedLcalcTests.Fixtures.AssumedCurve11
public import VerifiedLcalcTests.Fixtures.Curve11Central
public import VerifiedLcalc.Certification.CentralEvaluator

@[expose] public section
open VerifiedLcalc
namespace VerifiedLcalcTests.Fixtures.AssumedCurve11Central
open EllipticCurve Modularity
open AssumedCurve11

abbrev W : WeierstrassCurve ℚ := WeierstrassCurve.baseChange Examples.curve11 ℚ

/-- Actual prime coefficients, using the explicitly assumed modular
realization's good-prime compatibility and its full coefficient matching. -/
theorem prime_coefficient (p : ℕ) (hp : p.Prime)
    (hg : goodReduction Examples.curve11 p = true) :
    W.LFunction p = computeFrobeniusTrace Examples.curve11 p := by
  have h := realization.goodPrimeCoefficients_computed p hp hg
  rw [realization.coefficients] at h
  exact_mod_cast h

/-- The saved eight-term payload is a prefix of the actual curve L-function.
The coefficient at 2 is -2, which rules out bad reduction in the actual local
factor and determines the coefficients at 4 and 8 by the proved recurrence. -/
theorem actual_prefix : Central_11_a2_M8_P53_plus.result.coefficients =
    (List.range Central_11_a2_M8_P53_plus.result.termLimit).map
      (fun j => W.LFunction (j + 1)) := by
  have h1 : W.LFunction 1 = 1 := W.LFunction_apply_one
  have h2 : W.LFunction 2 = -2 :=
    (prime_coefficient 2 (by decide) (by decide)).trans (by decide)
  have h3 : W.LFunction 3 = -1 :=
    (prime_coefficient 3 (by decide) (by decide)).trans (by decide)
  have h5 : W.LFunction 5 = 1 :=
    (prime_coefficient 5 (by decide) (by decide)).trans (by decide)
  have h7 : W.LFunction 7 = -2 :=
    (prime_coefficient 7 (by decide) (by decide)).trans (by decide)
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨q, hq, _, _, hr, hb⟩ := LFunction_primePower_recurrence W 2
  have hq2 : q = 2 := by
    rcases hq with hq | hq
    · exact hq
    · have h := hb hq
      norm_num [h2] at h
  have h4 : W.LFunction 4 = 2 := by
    have h := hr 2
    norm_num [h2, hq2, localCoefficient, localPair] at h
    exact h
  have h8 : W.LFunction 8 = 0 := by
    have h := hr 3
    norm_num [h2, hq2, localCoefficient, localPair] at h
    exact h
  have h6 : W.LFunction 6 = 2 := by
    have h := W.isMultiplicative_LFunction.map_mul_of_coprime (by decide : Nat.Coprime 2 3)
    norm_num [h2, h3] at h
    exact h
  change [1, -2, -1, 2, 1, 2, -2, 0] =
    [W.LFunction 1, W.LFunction 2, W.LFunction 3, W.LFunction 4,
      W.LFunction 5, W.LFunction 6, W.LFunction 7, W.LFunction 8]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]

/-- Complete certificate for 11.a2. Its only custom axiom is the unchanged
ellipticModularity assumption; there are no remaining arithmetic or numerical
proof arguments. This proves exact analytic order zero at the center s=1. -/
theorem analytic_rank_zero : analyticOrderAt continuedL (1 : ℂ) = 0 := by
  apply realization.analyticOrder_zero_of_centralCoefficients
    Central_11_a2_M8_P53_plus.result Central_11_a2_M8_P53_plus.payload_correct
    (by rfl)
    (by change 11 = realization.level; exact realization_level.symm)
    (by change 1 = realization.rootNumber; exact realization_sign.symm)
    actual_prefix
  decide +kernel

/-- Executable data paired with the checked exact-rank theorem. The proof is
erased when this value is evaluated, while its type retains the specification. -/
def certifiedRank : {n : ℕ // analyticOrderAt continuedL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

theorem certifiedRank_correct : analyticOrderAt continuedL (1 : ℂ) = certifiedRank.val :=
  certifiedRank.property

end VerifiedLcalcTests.Fixtures.AssumedCurve11Central
