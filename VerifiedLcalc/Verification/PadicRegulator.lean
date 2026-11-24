/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Analytic
public import VerifiedLcalc.EllipticCurve.Arithmetic
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

end VerifiedLcalc.Certification
