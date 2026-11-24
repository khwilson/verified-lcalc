import VerifiedLcalc.Verification.Precision
import VerifiedLcalcTests.Fixtures.NumericalQuartic
import Lean

/-! # Exact analytic rank under explicit derivative-gap hypotheses -/

open Lean Elab Command VerifiedLcalc VerifiedLcalc.NumericalRanks

/-- This conclusion explicitly requires the named additional gap hypothesis.
The example is a polynomial, not a fabricated elliptic rank-four certificate. -/
theorem quartic_rank_from_explicit_gap
    (gap : NonzeroDerivativeGap (fun z : ℂ => z ^ 4) 0 4 (1 / 16777216)) :
    analyticOrderAt (fun z : ℂ => z ^ 4) 0 = 4 := by
  apply rank_eq_of_small_gap
    (show AnalyticAt ℂ (fun z : ℂ => z ^ 4) 0 from by fun_prop)
    VerifiedLcalcTests.Fixtures.NumericalQuartic.certified_small_derivatives gap
    (show (1 / 33554432 : Rat) < 1 / 16777216 from by decide +kernel)
  norm_num [iteratedDeriv_fun_pow_zero]

/-- Precision-small nonzero constants violate the required gap assumption. -/
theorem small_constant_has_no_claimed_gap :
    ¬ NonzeroDerivativeGap (fun _ : ℂ => (1 / 67108864 : ℂ))
      0 4 (1 / 16777216) := by
  intro separated
  have hn : iteratedDeriv 0 (fun _ : ℂ => (1 / 67108864 : ℂ)) 0 ≠ 0 := by
    norm_num
  have bound := separated 0 (by decide) hn
  norm_num at bound

/-- Equality at the cutoff cannot replace the required strict margin. -/
theorem cutoff_boundary_is_not_zero :
    SmallDerivatives (fun _ : ℂ => (1 / 33554432 : ℂ)) 0 1 (1 / 33554432) ∧
    NonzeroDerivativeGap (fun _ : ℂ => (1 / 33554432 : ℂ)) 0 1 (1 / 33554432) ∧
    analyticOrderAt (fun _ : ℂ => (1 / 33554432 : ℂ)) 0 = 0 := by
  constructor
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num
  constructor
  · intro k hk _
    have hk0 : k = 0 := by omega
    subst k
    left
    norm_num
  · apply (analyticAt_const :
      AnalyticAt ℂ (fun _ : ℂ => (1 / 33554432 : ℂ)) 0).analyticOrderAt_eq_zero.mpr
    norm_num

-- The generic bridge must have no project-specific mathematical assumptions.
run_cmd do
  for name in [``exactVanishing_of_gap, ``lowerBound_of_small_gap,
      ``rank_eq_of_small_gap, ``quartic_rank_from_explicit_gap,
      ``small_constant_has_no_claimed_gap, ``cutoff_boundary_is_not_zero] do
    let axioms ← liftTermElabM <| Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
  for name in [``Certification.AssumedExactEvidence.mk,
      ``Certification.AssumedNumericalEvidence.mk,
      ``Assumptions.CurvePrecisionClaim.Hypotheses.mk] do
    let axioms ← liftTermElabM (Lean.collectAxioms name)
    unless axioms.contains ``Assumptions.ellipticModularity do
      throwError "Opt-in witness lost its modularity boundary: {name}"
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound,
          ``Assumptions.ellipticModularity].contains axiomName do
        throwError "Unexpected axiom in opt-in witness {name}: {axiomName}"
  for name in [``Assumptions.CurvePrecisionClaim.conditional_lower_bound,
      ``Assumptions.CurvePrecisionClaim.conditional_rank,
      ``Assumptions.check_numerical_with_curve_hypotheses] do
    let axioms ← liftTermElabM <| Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound,
          ``Assumptions.ellipticModularity].contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
