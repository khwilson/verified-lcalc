module

public import VerifiedLcalc.NumericalRankSoundness
public import VerifiedLcalcTests.Arithmetic.Monomial

@[expose] public section
open VerifiedLcalc

namespace VerifiedLcalcTests.Fixtures.NumericalQuartic

/-- Saved, immutable numerical policy and request. This is a polynomial example,
not an elliptic-curve rank certificate. -/
def request : NumericalRanks.Request :=
  { computation :=
      { formatVersion := 1
        subject := .monomial 4
        settings := ⟨53, 0, 4⟩
        build := ⟨"leanprover/lean4:v4.36.0-rc2",
          "3440367ed1804626334f13a3a534a9cbb3385a59",
          "polynomial-threshold-demo-v1", "numerical-prefix-checker-v1"⟩ }
    policy := ⟨53⟩ }

/-- Non-singleton boxes deliberately exercise the numerical rather than exact
vanishing checker. Every endpoint is stored as an exact rational. -/
def artifact : NumericalRanks.Artifact :=
  ⟨request, 4,
    [⟨-1 / 67108864, 1 / 67108864, 0, 0⟩,
     ⟨-1 / 67108864, 1 / 67108864, 0, 0⟩,
     ⟨-1 / 67108864, 1 / 67108864, 0, 0⟩,
     ⟨-1 / 67108864, 1 / 67108864, 0, 0⟩]⟩

theorem checked : NumericalRanks.check request artifact = true := by decide +kernel

def evidence : NumericalRanks.Evidence request artifact :=
  { function := fun z : ℂ => z ^ 4
    denotes := rfl
    analytic := by
      simpa [request, Artifacts.Subject.center] using
        (show AnalyticAt ℂ (fun z : ℂ => z ^ 4) 0 from by fun_prop)
    enclosures := by
      norm_num [artifact, request, Artifacts.Subject.center, Encloses, Box.Contains,
        Set.mem_Icc, iteratedDeriv_fun_pow_zero] }

/-- The unconditional theorem certified by the numerical payload. -/
theorem certified_small_derivatives :
    NumericalRanks.SmallDerivatives (fun z : ℂ => z ^ 4) 0 4 (1 / 33554432) := by
  have h := NumericalRanks.check_sound evidence checked
  norm_num [evidence, request, artifact, Artifacts.Subject.center, PrecisionPolicy.cutoff] at h
  exact h

/-- Any upgrade from numerical smallness to analytic rank has its additional
vanishing hypothesis explicitly visible in the theorem's type. -/
theorem conditional_analytic_lower_bound
    (hvanish : NumericalRanks.ExactVanishingHypothesis (fun z : ℂ => z ^ 4)
      0 4 (1 / 33554432)) :
    (4 : ℕ∞) ≤ analyticOrderAt (fun z : ℂ => z ^ 4) 0 := by
  have hv : NumericalRanks.ExactVanishingHypothesis evidence.function
      (request.computation.subject.center : ℂ) artifact.numericalLowerBound
      request.policy.cutoff := by
    norm_num [evidence, request, artifact, Artifacts.Subject.center, PrecisionPolicy.cutoff]
    exact hvanish
  simpa [evidence, request, artifact, Artifacts.Subject.center] using
    NumericalRanks.check_conditional_lowerBound evidence checked hv

-- Changing precision invalidates reuse, even if the boxes would also pass.
example : NumericalRanks.check { request with policy := ⟨64⟩ } artifact = false := by
  decide +kernel

-- An embedded policy must match the requested working precision.
example : NumericalRanks.check { request with policy := ⟨64⟩ }
    { artifact with request := { request with policy := ⟨64⟩ } } = false := by
  decide +kernel

-- Insufficient derivative coverage cannot support the numerical lower bound.
example : NumericalRanks.check request
    { artifact with derivativeBoxes := artifact.derivativeBoxes.take 3 } = false := by
  decide +kernel

-- A wide interval with midpoint zero cannot pass the cutoff test.
example : NumericalRanks.check request
    { artifact with derivativeBoxes :=
      ⟨-1, 1, 0, 0⟩ :: artifact.derivativeBoxes.drop 1 } = false := by
  decide +kernel

-- An inverted rectangle cannot pass either.
example : (Box.mk 1 (-1) 0 0).withinCutoff 1 = false := by decide +kernel

-- Threshold acceptance is intentionally insufficient for the exact checker.
example : scan artifact.derivativeBoxes = none := by decide +kernel

/-- A nonzero constant has four small derivatives under this policy but analytic
order zero. This prevents conflating the numerical and analytic statements. -/
theorem small_does_not_imply_rank_four :
    NumericalRanks.SmallDerivatives (fun _ : ℂ => (1 / 67108864 : ℂ))
      0 4 (1 / 33554432) ∧
    analyticOrderAt (fun _ : ℂ => (1 / 67108864 : ℂ)) 0 = 0 := by
  constructor
  · intro k hk
    by_cases hz : k = 0 <;> norm_num [iteratedDeriv_const, hz]
  · apply (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 / 67108864 : ℂ)) 0).analyticOrderAt_eq_zero.mpr
    norm_num

end VerifiedLcalcTests.Fixtures.NumericalQuartic
