/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.Canonical
public import VerifiedLcalc.Certificate.Witnesses.AssumedEvidence
public import VerifiedLcalc.NumericalRankSoundness
public import Mathlib.Analysis.Complex.CauchyIntegral

/-! Opt-in modular interpretations of exact and numerical certificate evidence. -/

@[expose] public section

namespace VerifiedLcalc.Certification
open Modularity EllipticCurve

/-- Axiom-dependent exact-rank theorem. The unchanged finite checker still
requires exact vanishing witnesses for all earlier derivatives. -/
theorem check_assumed_exact_sound {expected : Artifacts.Request} {artifact : Artifacts.Artifact}
    (e : AssumedExactEvidence expected artifact)
    (h : Artifacts.check expected artifact = true) :
    analyticOrderAt (modularWitness e.equation e.nonsingular).formL 1 = artifact.rank := by
  exact scan_analyticOrderAt
    ((modularWitness e.equation e.nonsingular).formL_differentiable.analyticAt 1)
    e.enclosures ((Artifacts.check_correct _ _).mp h).2.2.2.2

/-- The modularity assumption supplies the curve interpretation. The certified
numerical conclusion is still smallness rather than exact zero. -/
theorem check_assumed_numerical_sound {expected : NumericalRanks.Request}
    {artifact : NumericalRanks.Artifact} (e : AssumedNumericalEvidence expected artifact)
    (h : NumericalRanks.check expected artifact = true) :
    NumericalRanks.SmallDerivatives (modularWitness e.equation e.nonsingular).formL 1
      artifact.numericalLowerBound expected.policy.cutoff := by
  obtain ⟨_, _, _, _, _, hlen, hs⟩ := (NumericalRanks.check_correct _ _).mp h
  rw [← hlen]
  exact NumericalRanks.enclosures_small _ _ _ e.enclosures hs

/-- Any numerical-to-exact upgrade additionally depends on this explicit
vanishing hypothesis; it is not a consequence of the modularity axiom. -/
theorem check_assumed_numerical_lowerBound {expected : NumericalRanks.Request}
    {artifact : NumericalRanks.Artifact} (e : AssumedNumericalEvidence expected artifact)
    (h : NumericalRanks.check expected artifact = true)
    (hv : NumericalRanks.ExactVanishingHypothesis
      (modularWitness e.equation e.nonsingular).formL 1 artifact.numericalLowerBound
      expected.policy.cutoff) :
    (artifact.numericalLowerBound : ℕ∞) ≤
      analyticOrderAt (modularWitness e.equation e.nonsingular).formL 1 := by
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((modularWitness e.equation e.nonsingular).formL_differentiable.analyticAt 1)).mpr
  intro k hk
  exact hv k hk (check_assumed_numerical_sound e h k hk)

end VerifiedLcalc.Certification
