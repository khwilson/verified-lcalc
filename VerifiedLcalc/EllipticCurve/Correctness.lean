module

public import VerifiedLcalc.EllipticCurve.Arithmetic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Boolean reflection for the backend's collection/filter interface. -/
theorem isPrime_correct (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  simp [isPrime]

/-- The supplied model's Boolean discriminant test agrees with Mathlib reduction. -/
theorem goodReduction_correct (e : WeierstrassCurve ℤ) (p : Nat) :
    goodReduction e p = true ↔ (e.baseChange (ZMod p)).Δ ≠ 0 := by
  simp only [goodReduction, decide_eq_true_eq, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_Δ, eq_intCast, ne_eq,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]

/-- The optimized adapter preserves the finite-ring count at every nonzero
modulus, including composite moduli and characteristic two. -/
theorem computePointCount_eq_pointCountFinite (e : WeierstrassCurve ℤ) (p : ℕ)
    [NeZero p] : computePointCount e p = (e.baseChange (ZMod p)).pointCountFinite := by
  simp only [computePointCount, dif_neg (NeZero.ne p)]
  split
  · next hodd =>
    letI : Fact (Nat.Prime p) := ⟨hodd.1⟩
    exact WeierstrassCurve.pointCountOddFinite_correct _
      (by simpa only [ZMod.ringChar_zmod_n] using hodd.2)
  · rfl

/-- The Q-input adapter executes the canonical finite-field counting algorithm. -/
theorem computePointCount_correct (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    computePointCount e p = (e.baseChange (ZMod p)).pointCount := by
  rw [computePointCount_eq_pointCountFinite, WeierstrassCurve.pointCountFinite_eq_pointCount]

/-- The Q-input trace adapter agrees with TauCeti's existing Frobenius trace. -/
theorem computeFrobeniusTrace_correct (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] :
    computeFrobeniusTrace e p = (e.baseChange (ZMod p)).frobeniusTrace := by
  simp only [computeFrobeniusTrace, dif_neg (Fact.out : p.Prime).ne_zero]
  rw [computePointCount_correct, WeierstrassCurve.frobeniusTrace_def]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

/-- End-to-end arithmetic guarantee for every supported prime calculation. -/
theorem analysePrime_sound (e : WeierstrassCurve ℤ) (p : Nat) (d : PrimeData)
    (h : analysePrime e p = some d) :
    Nat.Prime p ∧ d.prime = p ∧
      d.points = Nat.card (e.baseChange (ZMod p)).toAffine.Point ∧
      d.trace = (p : Int) + 1 - Nat.card (e.baseChange (ZMod p)).toAffine.Point := by
  obtain ⟨hp, hg, hd, hpoints, htrace⟩ := analysePrime_correct e p d h
  have hp' := (isPrime_correct p).mp hp
  letI : Fact (Nat.Prime p) := ⟨hp'⟩
  have hΔ := (goodReduction_correct e p).mp hg
  letI : (e.baseChange (ZMod p)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have ht : computeFrobeniusTrace e p =
      (p : Int) + 1 - Nat.card (e.baseChange (ZMod p)).toAffine.Point := by
    rw [computeFrobeniusTrace_correct, WeierstrassCurve.frobeniusTrace_eq_card_point]
    rw [show Nat.card (ZMod p) = p by simp only [Nat.card_eq_fintype_card, ZMod.card]]
  have hc : computePointCount e p = Nat.card (e.baseChange (ZMod p)).toAffine.Point := by
    rw [computePointCount_correct, WeierstrassCurve.pointCount_eq_card_point]
  exact ⟨hp', hd, hpoints.trans hc, htrace.trans ht⟩

end VerifiedLcalc.EllipticCurve
