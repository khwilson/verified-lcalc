/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import VerifiedLcalc.Upstream.TauCeti.RingTheory.Localization.AtPrime

/-! Selected upstream excerpt: the DVR instance, the valuation bound and the
valuation-integers identification used by canonical global minimality.
See PROVENANCE.json for the exact source revision and omitted declarations. -/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {K : Type*} [Field K] [Algebra O K]
  [IsFractionRing O K] (v : HeightOneSpectrum O)

/-- The localisation of a Dedekind domain at a height-one prime is a discrete valuation ring. With
the `Algebra`, `IsScalarTower` and `IsFractionRing` instances of
`TauCeti/RingTheory/Localization/AtPrime.lean`, this is what lets Mathlib's theory over a discrete
valuation ring and its fraction field apply at each height-one prime of `O`. -/
instance isDiscreteValuationRing_localizationAtPrime :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _

/-- **Elements of the localisation at `v` have `v`-adic valuation at most one**, for any
`IsLocalization.AtPrime` model `S` of the localisation mapping to `K` over `O`, such as
`Localization.AtPrime v.asIdeal` with the instances above. Together with
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` this descends membership in
every localisation to membership in `O`. -/
theorem valuation_algebraMap_le_one_of_isLocalizationAtPrime {S : Type*} [CommRing S]
    [Algebra O S] [IsLocalization.AtPrime S v.asIdeal] [Algebra S K] [IsScalarTower O S K]
    (x : S) : v.valuation K (algebraMap S K x) ≤ 1 := by
  -- Write `x = r / s` with `s ∉ v`: the valuation of `s` is one and that of `r` at most one.
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl x
  dsimp only
  rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le (S := S) (T := K)
    v.asIdeal.primeCompl_le_nonZeroDivisors, valuation_of_mk',
    (v.intValuation_eq_one_iff_mem_primeCompl s).mpr s.2, div_one]
  exact v.intValuation_le_one r

/-- **The localisation at `v` is the ring of integers of the `v`-adic valuation on `K`.** The
result packages this identification as `Valuation.Integers`, making its unit and divisibility API
available for the localisation. -/
theorem integers_valuation_localizationAtPrime :
    (v.valuation K).Integers (Localization.AtPrime v.asIdeal) where
  hom_inj := IsFractionRing.injective _ K
  map_le_one := v.valuation_algebraMap_le_one_of_isLocalizationAtPrime
  exists_of_le_one := by
    intro x hx
    obtain ⟨a, s, hs, rfl⟩ : x ∈ valuationSubringAtPrime K v := by
      rw [valuationSubringAtPrime_eq_valuationSubring]; exact hx
    refine ⟨IsLocalization.mk' (Localization.AtPrime v.asIdeal) a ⟨s, hs⟩, ?_⟩
    have hs₀ : algebraMap O K s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (v.asIdeal.primeCompl_le_nonZeroDivisors hs)
    rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le
        (S := Localization.AtPrime v.asIdeal) (T := K)
        (h := v.asIdeal.primeCompl_le_nonZeroDivisors),
      IsLocalization.mk'_eq_iff_eq_mul]
    field_simp


end IsDedekindDomain.HeightOneSpectrum

end
