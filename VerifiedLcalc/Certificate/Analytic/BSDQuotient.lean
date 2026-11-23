/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public import VerifiedLcalc.Numerics.RealIntervalCore
public import Mathlib.Algebra.Order.Round
import VerifiedLcalc.Numerics.RealInterval

/-! Compose proved input enclosures for the analytic BSD quotient over ℚ. -/

public section

namespace VerifiedLcalc
open Numerics

private theorem centered_contains_iff {center radius : ℚ} {x : ℝ} :
    RealInterval.Contains (center - radius, center + radius) x ↔
      |x - (center : ℝ)| ≤ (radius : ℝ) := by
  simp only [RealInterval.Contains, Rat.cast_sub, Rat.cast_add, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem reciprocal_contains (bounds : RealInterval) (x : ℝ)
    (hx : bounds.Contains x) (hpos : 0 < bounds.1) :
    RealInterval.Contains (bounds.2⁻¹, bounds.1⁻¹) x⁻¹ := by
  have hlo : 0 < (bounds.1 : ℝ) := by exact_mod_cast hpos
  have hxpos := hlo.trans_le hx.1
  exact ⟨by simpa [one_div] using one_div_le_one_div_of_le hxpos hx.2,
    by simpa [one_div] using one_div_le_one_div_of_le hlo hx.1⟩

variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]

/-- Rational interval for the product of the period, regulator and Tamagawa factors. -/
@[expose] def AnalyticShaFact.denominatorBounds (period : RealPeriodFact curve)
    (regulator : RegulatorFacts (curve.baseChange ℚ)) (tamagawa : TamagawaProductFact curve) :
    RealInterval :=
  intervalMul (intervalMul
    (period.reported - period.error.val, period.reported + period.error.val)
    (regulator.reported - regulator.error, regulator.reported + regulator.error))
    (tamagawa.value, tamagawa.value)

/-- Compose the leading coefficient, torsion, period, regulator and Tamagawa intervals.
The enclosure is sound when the lower endpoint of `denominatorBounds` is strictly positive. -/
@[expose] def AnalyticShaFact.quotientBounds (leading : SpecialLValueFacts curve)
    (torsion : { n : ℕ //
      Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n })
    (period : RealPeriodFact curve) (regulator : RegulatorFacts (curve.baseChange ℚ))
    (tamagawa : TamagawaProductFact curve) : RealInterval :=
  let numerator := intervalMul
    (leading.claim.reported - leading.claim.error, leading.claim.reported + leading.claim.error)
    ((torsion.val : ℚ) ^ 2, (torsion.val : ℚ) ^ 2)
  let den := denominatorBounds period regulator tamagawa
  intervalMul numerator (den.2⁻¹, den.1⁻¹)

/-- The intrinsic product lies in the computed denominator interval. -/
theorem AnalyticShaFact.denominatorBounds_contains (period : RealPeriodFact curve)
    (regulator : RegulatorFacts (curve.baseChange ℚ)) (tamagawa : TamagawaProductFact curve) :
    let E := curve.baseChange ℚ
    (AnalyticShaFact.denominatorBounds period regulator tamagawa).Contains
      (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ)) := by
  dsimp only
  have ht : RealInterval.Contains (tamagawa.value, tamagawa.value)
      ((curve.baseChange ℚ).tamagawaProduct (R := ℤ) : ℝ) := by
    simp [RealInterval.Contains, tamagawa.correct]
  exact intervalMul_sound _ _ _ _ (intervalMul_sound _ _ _ _
      (centered_contains_iff.mpr period.correct)
      (centered_contains_iff.mpr regulator.within_error)) ht

/-- Every explicit realization has analytic BSD quotient within the computed interval. -/
theorem AnalyticShaFact.quotientBounds_contains (leading : SpecialLValueFacts curve)
    (torsion : { n : ℕ //
      Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n })
    (period : RealPeriodFact curve) (regulator : RegulatorFacts (curve.baseChange ℚ))
    (tamagawa : TamagawaProductFact curve)
    (positive : 0 < (denominatorBounds period regulator tamagawa).1)
    (m : Modularity.ArithmeticModularRealization curve) :
    let E := curve.baseChange ℚ
    (quotientBounds leading torsion period regulator tamagawa).Contains
      ((iteratedDeriv leading.order m.formL 1).re / (leading.order.factorial : ℝ) *
        (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
        (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ))) := by
  let E := curve.baseChange ℚ
  have hden := denominatorBounds_contains period regulator tamagawa
  have ht :
      RealInterval.Contains ((torsion.val : ℚ) ^ 2, (torsion.val : ℚ) ^ 2)
        ((Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2) := by
    simp [RealInterval.Contains, E, torsion.property]
  have hq := intervalMul_sound _ _ _ _
    (intervalMul_sound _ _ _ _ (centered_contains_iff.mpr (leading.correct m).2) ht)
    (reciprocal_contains _ _ hden positive)
  change (quotientBounds leading torsion period regulator tamagawa).Contains _ at hq
  rw [div_eq_mul_inv]
  exact hq

/-- Build an analytic BSD quotient fact from proved factors and finite rational comparisons.
The submitted error interval must contain the interval computed for the quotient. -/
@[expose] def AnalyticShaFact.ofFactors (leading : SpecialLValueFacts curve)
    (torsion : { n : ℕ //
      Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n })
    (period : RealPeriodFact curve) (regulator : RegulatorFacts (curve.baseChange ℚ))
    (tamagawa : TamagawaProductFact curve) (reported : ℚ) (error : { ε : ℚ // 0 ≤ ε })
    (positive : 0 < (denominatorBounds period regulator tamagawa).1)
    (lower : reported - error.val ≤
      (quotientBounds leading torsion period regulator tamagawa).1)
    (upper : (quotientBounds leading torsion period regulator tamagawa).2 ≤
      reported + error.val) :
    AnalyticShaFact curve where
  order := leading.order
  reported := reported
  error := error
  order_correct m := (leading.correct m).1
  denominator_pos := by
    have hpos : (0 : ℝ) < ((denominatorBounds period regulator tamagawa).1 : ℝ) := by
      exact_mod_cast positive
    exact hpos.trans_le (denominatorBounds_contains period regulator tamagawa).1
  correct m := by
    dsimp only
    have hq := quotientBounds_contains leading torsion period regulator tamagawa positive m
    let bounds := quotientBounds leading torsion period regulator tamagawa
    have hlo : (reported : ℝ) - (error.val : ℝ) ≤ (bounds.1 : ℝ) := by
      exact_mod_cast lower
    have hhi : (bounds.2 : ℝ) ≤ (reported : ℝ) + (error.val : ℝ) := by
      exact_mod_cast upper
    exact abs_sub_le_iff.mpr ⟨by linarith only [hq.2.trans hhi],
      by linarith only [hlo.trans hq.1]⟩

/-- The actual quotient for each explicit realization rounds to the certified positive integer. -/
theorem RoundedAnalyticShaFact.round_eq (fact : RoundedAnalyticShaFact curve)
    (m : Modularity.ArithmeticModularRealization curve) :
    let E := curve.baseChange ℚ
    round ((iteratedDeriv fact.analytic.order m.formL 1).re /
        (fact.analytic.order.factorial : ℝ) *
        (Nat.card (AddCommGroup.torsion E.toAffine.Point) : ℝ) ^ 2 /
        (E.minimalRealPeriod * E.toAffine.regulator * E.tamagawaProduct (R := ℤ))) =
      (fact.value : ℤ) := by
  have hr : |(fact.analytic.reported : ℝ) - (fact.value : ℝ)| +
      (fact.analytic.error.val : ℝ) < 1 / 2 := by
    simpa only [Rat.cast_add, Rat.cast_abs, Rat.cast_sub, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr fact.rounds
  have hc := fact.analytic.correct m
  dsimp only at hc ⊢
  apply round_eq_iff.mpr
  rw [Set.mem_Ico]
  push_cast
  have hclose (q : ℝ) (hq : |q - (fact.analytic.reported : ℝ)| ≤ fact.analytic.error.val) :
      |q - (fact.value : ℝ)| < 1 / 2 := calc
    _ ≤ |q - (fact.analytic.reported : ℝ)| + |(fact.analytic.reported : ℝ) - fact.value| := by
      convert abs_add_le (q - (fact.analytic.reported : ℝ))
        ((fact.analytic.reported : ℝ) - fact.value) using 2
      ring
    _ < 1 / 2 := by linarith only [hq, hr]
  have h := abs_lt.mp (hclose _ hc)
  constructor <;> linarith only [h.1, h.2]

end VerifiedLcalc
