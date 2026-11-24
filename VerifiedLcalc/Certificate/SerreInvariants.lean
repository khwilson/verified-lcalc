/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import TauCeti.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.RingTheory.Radical.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # The usual conductor in the semistable Serre recipe -/

public section

namespace VerifiedLcalc

open WeierstrassCurve UniqueFactorizationMonoid NumberField

/-- The usual conductor in the semistable Serre recipe is the absolute norm of the
curve's algorithmic conductor. -/
theorem SemistableSerreRecipeFact.usualConductor_eq {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (fact : SemistableSerreRecipeFact curve) :
    (usualSerrePair curve.Δ.natAbs).2 =
      Ideal.absNorm (algorithmicConductor (𝓞 ℚ) (curve.baseChange ℚ)) := by
  let e := Rat.ringOfIntegersEquiv
  let : IsPrincipalIdealRing (𝓞 ℚ) := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let : StrongNormalizationMonoid (𝓞 ℚ) := UniqueFactorizationMonoid.strongNormalizationMonoid
  have hd : algebraMap (𝓞 ℚ) ℚ (e.symm curve.Δ) = (curve.baseChange ℚ).Δ := by
    change ((e.symm curve.Δ : 𝓞 ℚ) : ℚ) = _
    rw [Rat.ringOfIntegersEquiv_symm_apply_coe, WeierstrassCurve.baseChange, map_Δ]
    rfl
  have hd0 : e.symm curve.Δ ≠ 0 := by
    intro h
    have hz : (curve.baseChange ℚ).Δ = 0 := by simpa [h] using hd.symm
    exact ((curve.baseChange ℚ).coe_Δ' ▸ (curve.baseChange ℚ).Δ'.ne_zero) hz
  have hn : curve.Δ ≠ 0 := fun h => hd0 (by simp [h])
  have hcond : algorithmicConductor (𝓞 ℚ) (curve.baseChange ℚ) =
      radical (minimalDiscriminantIdeal (𝓞 ℚ) (curve.baseChange ℚ)) :=
    (isSemistable_iff_algorithmicConductor_eq_radical (O := 𝓞 ℚ)
      (curve.baseChange ℚ)).mp fact.semistable
  rw [hcond,
    minimalDiscriminantIdeal_eq_span_of_isGlobalMinimal fact.minimal hd, radical_span_singleton,
    ← Ideal.radical_span_singleton_eq_span_radical hd0, ← Ideal.absNorm_map_of_ringEquiv e]
  rw [← Ideal.comap_symm e, Ideal.comap_radical, Ideal.comap_symm e,
    Ideal.map_span, Set.image_singleton]
  change _ = Ideal.absNorm (Ideal.span {e (e.symm curve.Δ)}).radical
  rw [e.apply_symm_apply, Ideal.radical_span_singleton_eq_span_radical hn,
    Int.absNorm_span_singleton, ← Int.radical_natAbs_eq_radical,
    Int.natAbs_natCast, Nat.radical_eq_prod_primeFactors]
  rfl

end VerifiedLcalc
