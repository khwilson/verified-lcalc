module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import VerifiedLcalc.EllipticCurve.BadPrime
public import VerifiedLcalc.EllipticCurve.GlobalMinimality
public import VerifiedLcalc.EllipticCurve.Residue
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Semistable

/-! # Reduction of minimal integral models at rational primes

Relate the canonical reduction predicates over the local ring to divisibility of the
integral invariants and to the node polynomial over `ZMod p`.
-/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve

/-- The local ring at the rational prime, using the same localization as global minimality. -/
abbrev RationalLocalRing (p : Nat) [Fact p.Prime] :=
  Localization.AtPrime (rationalPlace p).asIdeal

private noncomputable def residueFieldEquivZMod (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField (RationalLocalRing p) ≃+* ZMod p := by
  let v := rationalPlace p
  letI : v.asIdeal.IsMaximal := (inferInstance : v.asIdeal.IsPrime).isMaximal v.ne_bot
  have f := (RingEquiv.ofBijective (algebraMap (𝓞 ℚ ⧸ v.asIdeal) v.asIdeal.ResidueField)
    v.asIdeal.bijective_algebraMap_quotient_residueField).symm.trans (idealQuotientEquivZMod v)
  rw [rationalPlace_norm p] at f
  exact f

private theorem int_valuation_eq_one_iff (p : ℕ) [Fact p.Prime] (n : ℤ) :
    valuation ℚ (IsDiscreteValuationRing.maximalIdeal (RationalLocalRing p)) (n : ℚ) = 1 ↔
      ¬ (p : ℤ) ∣ n := by
  let R := RationalLocalRing p
  let f := residueFieldEquivZMod p
  have hcast : f (IsLocalRing.residue R (n : R)) = (n : ZMod p) := by
    change (f.toRingHom.comp (IsLocalRing.residue R)) (n : R) = _
    exact map_intCast _ _
  rw [← map_intCast (algebraMap R ℚ),
    (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem]
  change (n : R) ∉ IsLocalRing.maximalIdeal R ↔ _
  rw [← IsLocalRing.residue_eq_zero_iff, ← f.map_eq_zero_iff, hcast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem int_valuation_lt_one_iff (p : Nat) [Fact p.Prime] (n : Int) :
    valuation ℚ (IsDiscreteValuationRing.maximalIdeal (RationalLocalRing p)) (n : ℚ) < 1 ↔
      (p : Int) ∣ n := by
  let R := RationalLocalRing p
  have hle : valuation ℚ (IsDiscreteValuationRing.maximalIdeal R) (n : ℚ) ≤ 1 := by
    simpa only [map_intCast] using
      ((IsDiscreteValuationRing.maximalIdeal R).valuation_le_one (K := ℚ) (n : R))
  rw [lt_iff_le_and_ne, and_iff_right hle, ne_eq, int_valuation_eq_one_iff, not_not]

/-- A minimal integral equation has additive reduction when both invariants vanish modulo `p`. -/
theorem hasAdditiveReduction_at_iff (e : WeierstrassCurve ℤ) (p : Nat) [Fact p.Prime]
    [IsMinimal (RationalLocalRing p) (e.baseChange ℚ)] :
    (e.baseChange ℚ).HasAdditiveReduction (RationalLocalRing p) ↔
      (p : Int) ∣ e.Δ ∧ (p : Int) ∣ e.c₄ := by
  rw [hasAdditiveReduction_iff, and_iff_right_of_imp]
  · simp only [WeierstrassCurve.baseChange, map_Δ, map_c₄, eq_intCast, int_valuation_lt_one_iff]
  · intro _
    infer_instance

/-- A minimal integral equation has multiplicative reduction when only its discriminant vanishes
modulo `p`. -/
theorem hasMultiplicativeReduction_at_iff (e : WeierstrassCurve ℤ) (p : Nat) [Fact p.Prime]
    [IsMinimal (RationalLocalRing p) (e.baseChange ℚ)] :
    (e.baseChange ℚ).HasMultiplicativeReduction (RationalLocalRing p) ↔
      (p : Int) ∣ e.Δ ∧ ¬ (p : Int) ∣ e.c₄ := by
  rw [hasMultiplicativeReduction_iff, and_iff_right_of_imp]
  · simp only [WeierstrassCurve.baseChange, map_Δ, map_c₄, eq_intCast,
      int_valuation_lt_one_iff, int_valuation_eq_one_iff]
  · intro _
    infer_instance

/-- Over the local ring at `p`, split multiplicative reduction is detected by the node
polynomial over `ZMod p` once the integral equation has multiplicative reduction. -/
theorem hasSplitMultiplicativeReduction_at_iff (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hm : (e.baseChange ℚ).HasMultiplicativeReduction (RationalLocalRing p)) :
    (e.baseChange ℚ).HasSplitMultiplicativeReduction (RationalLocalRing p) ↔
      (e.baseChange (ZMod p)).nodePolynomial.Splits := by
  let R := RationalLocalRing p
  let f := residueFieldEquivZMod p
  let := hm.toIsMinimal
  have hmodel : (e.baseChange ℚ).integralModel R = e.baseChange R := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective R ℚ)
    exact (baseChange_integralModel_eq R _).trans <| by
      ext <;> simp [WeierstrassCurve.baseChange]
  have hmap : (f.toRingHom.comp (IsLocalRing.residue R)).comp (algebraMap ℤ R) =
      algebraMap ℤ (ZMod p) := Subsingleton.elim _ _
  have hreduce : ((e.baseChange ℚ).reduction R).map f.toRingHom = e.baseChange (ZMod p) := by
    rw [WeierstrassCurve.reduction, hmodel]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    rw [← RingHom.comp_assoc, hmap]
  rw [← hm.splits_nodePolynomial_reduction_iff R, ← hreduce, map_nodePolynomial]
  exact ⟨fun h => h.map f.toRingHom,
    fun h => h.of_splits_map f.toRingHom (fun x _ => f.surjective x)⟩

/-- The canonical semistability condition can be read on a checked global minimal model. -/
theorem semistable_iff_coprime_of_isGlobalMinimal (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] (hm : IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ)) :
    IsSemistable (𝓞 ℚ) (e.baseChange ℚ) ↔ Int.gcd e.Δ e.c₄ = 1 := by
  have hlocal (p : Nat) [Fact p.Prime] :
      ¬ ((e.baseChange ℚ).minimal (RationalLocalRing p)).HasAdditiveReduction
          (RationalLocalRing p) ↔ ¬ ((p : Int) ∣ e.Δ ∧ (p : Int) ∣ e.c₄) := by
    let R := RationalLocalRing p
    let := hm.isMinimal (rationalPlace p)
    obtain ⟨C, hC⟩ := (e.baseChange ℚ).exists_smul_eq_minimal R
    rw [hasAdditiveReduction_iff_of_isMinimal_smul R C hC, hasAdditiveReduction_at_iff]
  rw [isSemistable_iff, Nat.eq_one_iff_not_exists_prime_dvd]
  constructor
  · intro h p hp hd
    let : Fact p.Prime := ⟨hp⟩
    exact (hlocal p).mp (h (rationalPlace p)) (by
      simpa only [Int.gcd, Nat.dvd_gcd_iff, Int.natCast_dvd] using hd)
  · intro h v
    let : Fact v.asIdeal.absNorm.Prime := ⟨RationalPrimes.norm_prime v⟩
    have hv : rationalPlace v.asIdeal.absNorm = v :=
      RationalPrimes.norm_injective (rationalPlace_norm v.asIdeal.absNorm)
    rw [← hv]
    apply (hlocal _).mpr
    simpa only [Int.gcd, Nat.dvd_gcd_iff, Int.natCast_dvd] using h _ Fact.out

end VerifiedLcalc.EllipticCurve
