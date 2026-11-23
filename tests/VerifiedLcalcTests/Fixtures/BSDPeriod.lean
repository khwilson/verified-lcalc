/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.RealPeriod
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The full real period of 17.a2

The equation and decimal come from https://www.lmfdb.org/EllipticCurve/Q/data/17.a2.
TauCeti's three-real-root AGM identity gives an enclosure with an explicit radius.
-/

@[expose] public section

open VerifiedLcalc WeierstrassCurve Real NNReal

namespace Curve17a2

/-- The integral equation of 17.a2. -/
def model : WeierstrassCurve ℤ := ⟨1, -1, 1, -6, -4⟩

instance : (model.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

private theorem minimal : IsGlobalMinimal ℤ (model.baseChange ℚ) := by
  apply isGlobalMinimal_baseChange_of_isCoprime
  change IsCoprime (289 : ℤ) 273
  exact ⟨-17, 18, by decide⟩

private theorem enclosed :
    |2 * Real.pi /
          (NNReal.agm (Real.sqrt (3 - (-5 / 4))).toNNReal (Real.sqrt (3 - (-1))).toNNReal : ℝ) -
        3.0941595071022403464191580099| ≤ 0.06 := by
  let a := (Real.sqrt (3 - (-5 / 4))).toNNReal
  let b := (Real.sqrt (3 - (-1))).toNNReal
  have ha : (2 : ℝ) ≤ (a : ℝ) ∧ (a : ℝ) ≤ 2.065 := by
    rw [show (a : ℝ) = Real.sqrt (3 - (-5 / 4)) from Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    constructor <;> nlinarith [Real.sq_sqrt (show 0 ≤ (3 - -5 / 4 : ℝ) by norm_num),
      Real.sqrt_nonneg (3 - -5 / 4)]
  have hb : (b : ℝ) = 2 := by
    change ((Real.sqrt (3 - (-1))).toNNReal : ℝ) = 2
    rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have hlo : (2 : ℝ) ≤ NNReal.agm a b := by
    calc
      _ ≤ min (a : ℝ) (b : ℝ) := le_min ha.1 hb.ge
      _ ≤ _ := NNReal.min_le_agm
  have hhi : (NNReal.agm a b : ℝ) ≤ 2.065 := by
    calc
      _ ≤ max (a : ℝ) (b : ℝ) := NNReal.agm_le_max
      _ ≤ _ := max_le ha.2 (by rw [hb]; norm_num)
  have hpos : 0 < (NNReal.agm a b : ℝ) := by linarith
  apply abs_le.mpr
  constructor
  · apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ hpos).mpr
    linarith [Real.pi_gt_d2]
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hpos).mpr
    linarith [Real.pi_lt_d2]

/-- A rational decimal enclosure for the full minimal period of 17.a2. -/
theorem period_enclosure :
    |(model.baseChange ℚ).minimalRealPeriod - 3.0941595071022403464191580099| ≤ 0.06 := by
  rw [minimal.minimalRealPeriod_eq]
  let W := (model.baseChange ℚ).baseChange ℝ
  have hpoly (x : ℝ) : W.Ψ₂Sq.eval x = 4 * (x - 3) * (x - (-1)) * (x - (-5 / 4)) := by
    simp [W, model, Ψ₂Sq, b₂, b₄, b₆, baseChange, map]
    ring
  rw [W.realPeriod_eq_two_mul_pi_div_agm_of_three_real_roots (by norm_num) (by norm_num) hpoly]
  exact enclosed

/-- The exact reported center and explicit radius, with the AGM bound attached. -/
def period : RealPeriodFact model :=
  ⟨30941595071022403464191580099 / 10000000000000000000000000000,
    ⟨3 / 50, by decide +kernel⟩, by
    convert period_enclosure using 1 <;> norm_num⟩

certify_ec PeriodCertificate from_json_string
  r#"{"ainvs":[1,-1,1,-6,-4],"real_period":"3.0941595071022403464191580099",
      "real_period_evidence":{"error":"3/50"}}"#
  with_proofs { realPeriod := some period }

end Curve17a2
