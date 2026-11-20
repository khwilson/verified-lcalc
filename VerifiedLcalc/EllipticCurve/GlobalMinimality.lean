module

public import VerifiedLcalc.EllipticCurve.ReductionArithmetic
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain WeierstrassCurve

private theorem rationalPlace_valuation_intCast (p : ℕ) [Fact p.Prime] (n : ℤ) :
    (rationalPlace p).valuation ℚ (n : ℚ) =
      (rationalPlace p).intValuation (n : 𝓞 ℚ) := by
  simpa only [map_intCast] using
    (rationalPlace p).valuation_of_algebraMap (K := ℚ) (n : 𝓞 ℚ)

private theorem integral_at_localization (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    IsIntegral (Localization.AtPrime (rationalPlace p).asIdeal) (e.baseChange ℚ) := by
  refine ⟨⟨e.baseChange (Localization.AtPrime (rationalPlace p).asIdeal), ?_⟩⟩
  ext <;> simp [WeierstrassCurve.baseChange]

/-- The discriminant criterion proves minimality directly over the canonical
localization, independently of completion-minimality comparisons. -/
theorem localization_minimal_of_discriminant_not_dvd (e : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime] (hd : ¬ (p : ℤ) ^ 12 ∣ e.Δ) :
    IsMinimal (Localization.AtPrime (rationalPlace p).asIdeal) (e.baseChange ℚ) := by
  letI := integral_at_localization e p
  apply minimal_of_small_discriminant (e.baseChange ℚ) ((rationalPlace p).valuation ℚ)
    ((rationalPlace p).integers_valuation_localizationAtPrime (K := ℚ))
  simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast,
    rationalPlace_valuation_intCast] using rationalPlace_intValuation_gt p 12 e.Δ hd

/-- Every branch of the finite minimality dispatcher works over the
localization used by TauCeti's global-minimality predicate. -/
theorem modelMinimalAt_localization (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (h : modelMinimalAt e p = true) :
    IsMinimal (Localization.AtPrime (rationalPlace p).asIdeal) (e.baseChange ℚ) := by
  letI := integral_at_localization e p
  have hv := (rationalPlace p).integers_valuation_localizationAtPrime (K := ℚ)
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases Bool.or_eq_true_iff.mp h with hd | htwo
    · exact localization_minimal_of_discriminant_not_dvd e p
        ((discriminantMinimalAt_correct e p).mp hd)
    · have ht : p = 2 ∧ e.c₄ % 64 = 0 ∧ e.c₄ % 128 ≠ 0 := by
        simpa only [twoAdicC4MinimalAt, decide_eq_true_eq] using htwo
      obtain ⟨rfl, h6, h7⟩ := ht
      apply isMinimal_of_two_adic_c4_six (e.baseChange ℚ) ((rationalPlace 2).valuation ℚ) hv
      · have h := completion_intCast_valuation_eq 2 1 2 (by decide) (by decide)
        rw [completion_intCast_valuation] at h
        rw [show (2 : ℚ) = algebraMap (𝓞 ℚ) ℚ (2 : 𝓞 ℚ) by simp only [map_ofNat],
          HeightOneSpectrum.valuation_of_algebraMap]
        simpa only [Int.cast_ofNat, Nat.cast_ofNat, Nat.cast_one] using h
      · rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, eq_intCast,
          rationalPlace_valuation_intCast, ← completion_intCast_valuation]
        apply completion_intCast_valuation_eq 2 6 e.c₄
        · have h6' : (64 : ℤ) ∣ e.c₄ := Int.dvd_iff_emod_eq_zero.mpr h6
          simpa only [Nat.cast_ofNat, Int.reducePow] using h6'
        · have h7' : ¬ (128 : ℤ) ∣ e.c₄ := mt Int.dvd_iff_emod_eq_zero.mp h7
          simpa only [Nat.cast_ofNat, Nat.reduceAdd, Int.reducePow] using h7'
  · have hi : ¬ (p : ℤ)^4 ∣ e.c₄ ∨ ¬ (p : ℤ)^6 ∣ e.c₆ := by
      simpa only [invariantMinimalAt, decide_eq_true_eq, ne_eq,
        Int.dvd_iff_emod_eq_zero] using h
    rcases hi with hc | hc
    · apply isMinimal_of_small_c4 (e.baseChange ℚ) ((rationalPlace p).valuation ℚ) hv
      simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, eq_intCast,
        rationalPlace_valuation_intCast] using rationalPlace_intValuation_gt p 4 e.c₄ hc
    · apply isMinimal_of_small_c6 (e.baseChange ℚ) ((rationalPlace p).valuation ℚ) hv
      simpa [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆, eq_intCast,
        rationalPlace_valuation_intCast] using rationalPlace_intValuation_gt p 6 e.c₆ hc

/-- The same checked witness supplies localization minimality without an
assumed equivalence between localization and completion minimality. -/
theorem localization_minimal_of_witness (e : WeierstrassCurve ℤ) (w : MinimalityWitness)
    (hw : w.Valid e) (p : ℕ) [Fact p.Prime] :
    IsMinimal (Localization.AtPrime (rationalPlace p).asIdeal) (e.baseChange ℚ) := by
  by_cases hpd : (p : ℤ) ∣ e.Δ
  · exact modelMinimalAt_localization e p (w.minimalAt_of_dvd hw Fact.out hpd)
  · apply localization_minimal_of_discriminant_not_dvd e p
    intro hd
    exact hpd (dvd_trans (dvd_pow_self (p : ℤ) (by decide : 12 ≠ 0)) hd)

/-- A checked finite witness proves TauCeti's actual global minimality at every
height-one prime, not a project-specific substitute for that predicate. -/
theorem globalMinimal_of_witness (e : WeierstrassCurve ℤ) (w : MinimalityWitness)
    (hw : w.Valid e) [(e.baseChange ℚ).IsElliptic] :
    IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ) := by
  apply IsGlobalMinimal.of_forall_isMinimal
  intro v
  obtain ⟨p, hp, rfl⟩ : ∃ (p : ℕ) (hp : p.Prime), v = @rationalPlace p ⟨hp⟩ := by
    letI : Fact (v.asIdeal.absNorm.Prime) := ⟨RationalPrimes.norm_prime v⟩
    refine ⟨v.asIdeal.absNorm, RationalPrimes.norm_prime v, ?_⟩
    exact (RationalPrimes.norm_injective (rationalPlace_norm v.asIdeal.absNorm)).symm
  letI : Fact p.Prime := ⟨hp⟩
  exact localization_minimal_of_witness e w hw p

end VerifiedLcalc.EllipticCurve
