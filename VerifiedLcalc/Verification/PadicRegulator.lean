/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Analytic
public import VerifiedLcalc.EllipticCurve.Arithmetic
import VerifiedLcalc.Verification.PadicLog
import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.Nat.Log
import VerifiedLcalc.EllipticCurve.Correctness
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Supersingular

/-! # Verification of rank-zero ordinary p-adic regulator balls -/

@[expose] public section

namespace VerifiedLcalc.Certification

open EllipticCurve

/-- The exact format check uses a ceiling logarithm to compare the unit to the
precision bound without constructing a large power of the prime. -/
def PadicRegulatorClaimValid (claim : PadicRegulatorClaim) : Prop :=
  claim.p.Prime ∧ claim.val < claim.prec ∧ ¬ (claim.p : ℤ) ∣ claim.unit ∧
    0 ≤ claim.unit ∧ Nat.clog claim.p (claim.unit.toNat + 1) ≤ (claim.prec - claim.val).toNat

instance (claim : PadicRegulatorClaim) : Decidable (PadicRegulatorClaimValid claim) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The format check is equivalent to the mathematical constraints on a normalized ball. -/
theorem padicRegulatorClaimValid_iff (claim : PadicRegulatorClaim) :
    PadicRegulatorClaimValid claim ↔
      claim.p.Prime ∧ claim.val < claim.prec ∧ ¬ (claim.p : ℤ) ∣ claim.unit ∧
        0 ≤ claim.unit ∧ claim.unit < (claim.p : ℤ) ^ (claim.prec - claim.val).toNat := by
  unfold PadicRegulatorClaimValid
  refine and_congr_right fun hp => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun nonnegative => ?_
  rw [Nat.clog_le_iff_le_pow hp.one_lt, ← Nat.lt_iff_add_one_le]
  exact_mod_cast (show claim.unit.toNat < claim.p ^ (claim.prec - claim.val).toNat ↔
    claim.unit < (claim.p : ℤ) ^ (claim.prec - claim.val).toNat by
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg nonnegative, Int.natCast_pow])

/-- An ordinary good prime is detected by the discriminant and the exact finite-field trace. -/
def goodOrdinaryPadicPrime (curve : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  goodReduction curve p && decide (¬ (p : ℤ) ∣ computeFrobeniusTrace curve p)

/-- A successful prime check proves smoothness and TauCeti's geometric ordinarity predicate. -/
theorem goodOrdinaryPadicPrime_sound (curve : WeierstrassCurve ℤ) (p : ℕ)
    [Fact p.Prime] (valid : goodOrdinaryPadicPrime curve p = true) :
    (curve.baseChange (ZMod p)).Δ ≠ 0 ∧ (curve.baseChange (ZMod p)).IsOrdinary p := by
  obtain ⟨hgood, htrace⟩ := Bool.and_eq_true_iff.mp valid
  have good := (goodReduction_correct curve p).mp hgood
  let : (curve.baseChange (ZMod p)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr good⟩
  refine ⟨good, (WeierstrassCurve.isOrdinary_iff_not_dvd_frobeniusTrace p _).mpr ?_⟩
  rw [← computeFrobeniusTrace_correct]
  exact of_decide_eq_true htrace

/-- Validate a normalized ball about the actual rank-zero ordinary height determinant.
The center is one at its stated precision, with valuation zero and unit one. -/
def rankZeroPadicRegulatorFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (claim : PadicRegulatorClaim)
    (valid : PadicRegulatorClaimValid claim)
    (prime : goodOrdinaryPadicPrime curve claim.p = true)
    (rankZero : Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = 0)
    (center : claim.val = 0 ∧ claim.unit = 1) : RankZeroPadicRegulatorFact curve := by
  let normalized := (padicRegulatorClaimValid_iff claim).mp valid
  letI : Fact claim.p.Prime := ⟨valid.1⟩
  have spec := goodOrdinaryPadicPrime_sound curve claim.p prime
  refine {
    report := ⟨⟨claim.p, valid.1⟩, claim.prec, claim.val, valid.2.1, claim.unit, valid.2.2.1⟩
    good := spec.1
    ordinary := spec.2
    normalized := normalized.2.2.2
    elliptic := inferInstance
    rankZero := rankZero
    contains := ?_ }
  change ‖rankZeroPadicRegulator (curve.baseChange ℚ) rankZero claim.p -
    (claim.p : ℚ_[claim.p]) ^ claim.val * (claim.unit : ℚ_[claim.p])‖ ≤
    (claim.p : ℝ) ^ (-claim.prec)
  rw [rankZeroPadicRegulator_eq_one, center.1, center.2]
  simpa using (zpow_nonneg (show 0 ≤ (claim.p : ℝ) by positivity) (-claim.prec))

/-- An executable form of the p-adic norm on rational numbers. -/
def rationalPadicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else
    (p : ℚ) ^ ((padicValNat p q.den : ℤ) - (padicValNat p q.num.natAbs : ℤ))

/-- The executable rational norm computes the norm in Mathlib's p-adic field
after embedding the rational number. -/
theorem rationalPadicNorm_eq (p : ℕ) (q : ℚ) :
    rationalPadicNorm p q = padicNorm p q := by
  simp [rationalPadicNorm, padicNorm, padicValRat, padicValInt, Nat.padicValNat_def, neg_sub]

/-- The exact finite arithmetic checks on the independent sigma-log argument.
The logarithm prefix is checked with a provable rounding and truncation budget. -/
def StoredPadicRegulatorValid (claim : PadicRegulatorClaim) (p n terms : ℕ)
    (approximation : ℚ) (approximationPrecision : ℤ) : Prop :=
  let radius := (p : ℚ) ^ (-claim.prec)
  let error := (p : ℚ) ^ (-approximationPrecision)
  let scale := ordinaryPadicHeightScale p n
  rationalPadicNorm p approximation ≤ (p : ℚ)⁻¹ ∧ error ≤ (p : ℚ)⁻¹ ∧
    rationalPadicNorm p scale * max ((terms : ℚ) * error) ((p : ℚ)⁻¹ * (2 / p : ℚ) ^ terms) ≤
      radius ∧
    rationalPadicNorm p (scale * rationalPadicLogPrefix approximation terms -
      (p : ℚ) ^ claim.val * (claim.unit : ℚ)) ≤ radius

instance (claim : PadicRegulatorClaim) (p n terms : ℕ) (w : ℚ) (prec : ℤ) :
    Decidable (StoredPadicRegulatorValid claim p n terms w prec) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The finite rational calculation is enclosed about the independently normalized height. -/
theorem storedPadicRegulator_contains (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (e : StoredPadicRegulatorEvidence curve)
    (claim : PadicRegulatorClaim)
    (arithmetic : StoredPadicRegulatorValid claim e.p e.multiple e.logTerms
      e.approximation e.approximationPrecision) :
    let p : ℕ := e.p
    letI : Fact p.Prime := ⟨e.p.property⟩
    ‖ordinaryPadicHeightAtMultiple e.sigma e.x e.y.val (e.denominator.1 : ℕ)
        (e.multiple : ℕ) - (p : ℚ_[p]) ^ claim.val * (claim.unit : ℚ_[p])‖ ≤
      (p : ℝ) ^ (-claim.prec) := by
  letI : Fact (e.p : ℕ).Prime := ⟨e.p.property⟩
  let p : ℕ := e.p
  let z := ordinarySigmaLogArgument e.sigma e.x e.y.val (e.denominator.1 : ℕ)
  let w : ℚ_[p] := (e.approximation : ℚ)
  let scale := ordinaryPadicHeightScale p e.multiple
  let approxSum := rationalPadicLogPrefix e.approximation e.logTerms
  let center : ℚ := (p : ℚ) ^ claim.val * (claim.unit : ℚ)
  have hw : ‖w‖ ≤ (p : ℝ)⁻¹ := by
    rw [show ‖w‖ = (rationalPadicNorm p e.approximation : ℝ) from (Padic.eq_padicNorm _).trans (congrArg Rat.cast (rationalPadicNorm_eq p _).symm)]
    simpa only [Rat.cast_inv, Rat.cast_natCast] using (Rat.cast_le.mpr arithmetic.1 : _ ≤ (_ : ℝ))
  have hzw : ‖z - w‖ ≤ (p : ℝ)⁻¹ :=
    e.approximation_correct.trans (by
      simpa only [Rat.cast_zpow, Rat.cast_inv, Rat.cast_natCast] using
        (Rat.cast_le.mpr arithmetic.2.1 : _ ≤ (_ : ℝ)))
  have hz : ‖z‖ ≤ (p : ℝ)⁻¹ := by
    rw [← sub_add_cancel z w]
    exact (IsUltrametricDist.norm_add_le_max ..).trans (max_le hzw hw)
  have hp : 2 < p := lt_trans (by decide) e.prime_gt_three
  have logBound := norm_padicLog_sub_prefix_le hp z e.approximation e.logTerms
    hz (hw.trans (inv_le_one_of_one_le₀ (by exact_mod_cast e.p.property.one_lt.le)))
  have hscale : ‖(scale : ℚ_[p])‖ = (rationalPadicNorm p scale : ℝ) :=
    (Padic.eq_padicNorm _).trans (congrArg Rat.cast (rationalPadicNorm_eq p _).symm)
  have hscaleNonneg : 0 ≤ (rationalPadicNorm p scale : ℝ) := hscale ▸ norm_nonneg _
  have hc : (center : ℚ_[p]) = (p : ℚ_[p]) ^ claim.val * (claim.unit : ℚ_[p]) := by
    simp [center]
  dsimp only
  rw [← hc]
  change ‖(scale : ℚ_[p]) * (∑' k, padicLogOneAddTerm z k) -
    (center : ℚ_[p])‖ ≤ (p : ℝ) ^ (-claim.prec)
  rw [← sub_add_sub_cancel _ ((scale * approxSum : ℚ) : ℚ_[p])]
  refine (IsUltrametricDist.norm_add_le_max ..).trans (max_le ?_ ?_)
  · rw [Rat.cast_mul, ← mul_sub, norm_mul, hscale]
    have hlog : ‖(∑' k, padicLogOneAddTerm z k) - (approxSum : ℚ_[p])‖ ≤
        max ((e.logTerms : ℝ) * (p : ℝ) ^ (-e.approximationPrecision))
          ((p : ℝ)⁻¹ * (2 / p : ℝ) ^ e.logTerms) := by
      exact logBound.trans
        (max_le_max (mul_le_mul_of_nonneg_left e.approximation_correct (by positivity)) le_rfl)
    refine (mul_le_mul_of_nonneg_left hlog hscaleNonneg).trans ?_
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_zpow, Rat.cast_max, Rat.cast_inv,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      (Rat.cast_le.mpr arithmetic.2.2.1 : _ ≤ (_ : ℝ))
  · rw [← Rat.cast_sub, Padic.eq_padicNorm, ← rationalPadicNorm_eq]
    simpa only [Rat.cast_zpow, Rat.cast_natCast] using
      (Rat.cast_le.mpr arithmetic.2.2.2 : _ ≤ (_ : ℝ))

/-- The finite comparison and the independent sigma argument enclosure give the
claimed ball about the normalized ordinary height. -/
def storedPadicRegulatorFact (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (e : StoredPadicRegulatorEvidence curve)
    (label : String)
    (label_eq : lmfdbIsoLabel e.roster.conductor e.roster.classIndex.val = label)
    (claim : PadicRegulatorClaim) (valid : PadicRegulatorClaimValid claim)
    (prime_eq : claim.p = e.p)
    (prime : goodOrdinaryPadicPrime curve e.p = true)
    (arithmetic : StoredPadicRegulatorValid claim e.p e.multiple e.logTerms
      e.approximation e.approximationPrecision) : StoredPadicRegulatorFact curve := by
  letI : Fact (e.p : ℕ).Prime := ⟨e.p.property⟩
  have normalized := (padicRegulatorClaimValid_iff claim).mp valid
  let spec := goodOrdinaryPadicPrime_sound curve e.p prime
  refine {
    elliptic := inferInstance
    evidence := e
    classLabel := label
    classLabel_eq := label_eq
    report := ⟨⟨claim.p, valid.1⟩, claim.prec, claim.val, valid.2.1, claim.unit, valid.2.2.1⟩
    prime_eq := prime_eq
    good := spec.1
    ordinary := spec.2
    normalized := normalized.2.2.2
    contains := storedPadicRegulator_contains curve e claim arithmetic }

/-- A native regulator ball fixes a nonzero normalized height and its exact valuation. -/
theorem _root_.VerifiedLcalc.StoredPadicRegulatorFact.valuation_eq
    {curve : WeierstrassCurve ℤ} (f : StoredPadicRegulatorFact curve) :
    letI := f.elliptic
    let p : ℕ := f.evidence.p
    letI : Fact p.Prime := ⟨f.evidence.p.property⟩
    let value := ordinaryPadicHeightAtMultiple f.evidence.sigma f.evidence.x f.evidence.y.val
      (f.evidence.denominator.1 : ℕ) (f.evidence.multiple : ℕ)
    value ≠ 0 ∧ value.valuation = f.report.val := by
  letI := f.elliptic
  let p : ℕ := f.evidence.p
  letI : Fact p.Prime := ⟨f.evidence.p.property⟩
  let value := ordinaryPadicHeightAtMultiple f.evidence.sigma f.evidence.x f.evidence.y.val
    (f.evidence.denominator.1 : ℕ) (f.evidence.multiple : ℕ)
  let center := (p : ℚ_[p]) ^ f.report.val * (f.report.unit : ℚ_[p])
  have hp : 1 < (p : ℝ) := by exact_mod_cast f.evidence.p.property.one_lt
  have hunit : ‖(f.report.unit : ℚ_[p])‖ = 1 := by
    apply le_antisymm (Padic.norm_int_le_one _)
    apply le_of_not_gt
    rw [Padic.norm_intCast_lt_one_iff]
    change ¬ ((f.evidence.p : ℕ) : ℤ) ∣ f.report.unit
    rw [← f.prime_eq]
    exact f.report.unit_not_dvd
  have hc : ‖center‖ = (p : ℝ) ^ (-f.report.val) := by
    rw [show center = (p : ℚ_[p]) ^ f.report.val * (f.report.unit : ℚ_[p]) from rfl,
      norm_mul, Padic.norm_p_zpow, hunit, mul_one]
  have hlt : ‖value - center‖ < ‖center‖ := by
    rw [hc]
    exact f.contains.trans_lt ((zpow_lt_zpow_iff_right₀ hp).mpr (by
      simpa only [neg_lt_neg_iff] using f.report.precise))
  have he := (Padic.norm_eq_of_norm_sub_lt_right hlt).trans hc
  have hn : value ≠ 0 := by
    intro h
    rw [h, norm_zero] at he
    exact (zpow_pos (zero_lt_one.trans hp) _).ne' he.symm
  rw [Padic.norm_eq_zpow_neg_valuation hn, zpow_right_inj₀ (zero_lt_one.trans hp) hp.ne',
    neg_inj] at he
  exact ⟨hn, he⟩

end VerifiedLcalc.Certification
