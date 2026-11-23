/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import TauCeti.NumberTheory.Height.Rat
import VerifiedLcalcTests.Arithmetic.TorsionBound

/-! # Explicit height enclosure for the generator of 37.a1

The [LMFDB report](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1) supplies
the coordinates and center. Clearing denominators in Mathlib's doubling
formula gives an upper bound on the change in naive height. Applying the
bound at eight times the generator gives a one-sided canonical height
bound. Together with nonnegativity it proves the reported enclosure.
-/

@[expose] public section

open Filter Height Topology WeierstrassCurve WeierstrassCurve.Affine VerifiedLcalc

namespace Height37

/-- The integral equation of 37.a1. -/
abbrev model : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩
/-- The rational base change for height computations. -/
abbrev W := model.baseChange ℚ
local instance : W.IsElliptic :=
  ⟨by norm_num [W, model, WeierstrassCurve.baseChange, map_Δ, Δ, b₂, b₄, b₆, b₈]⟩

private theorem affinePoint_not_torsion {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    ¬ IsOfFinAddOrder (Point.some x y h) := by
  intro ht
  have hcard : Nat.card (AddCommGroup.torsion W.toAffine.Point) = 1 :=
    VerifiedLcalcTests.TorsionBound.card_torsion_curve37a1
  have hsub := (Nat.card_eq_one_iff_unique.mp hcard).1
  let P : AddCommGroup.torsion W.toAffine.Point := ⟨.some x y h, ht⟩
  have hz := congrArg Subtype.val (@Subsingleton.elim _ hsub P 0)
  exact Point.some_ne_zero h hz

private theorem not_vertical {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    y ≠ W.toAffine.negY x y := by
  intro hy
  apply affinePoint_not_torsion h
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by decide, ?_⟩
  rw [two_nsmul, Point.add_self_of_Y_eq hy]

private def doublingNumerator (a b : ℤ) : ℤ :=
  a ^ 4 + 2 * a ^ 2 * b ^ 2 - 2 * a * b ^ 3 + b ^ 4

private def doublingDenominator (a b : ℤ) : ℤ :=
  4 * a ^ 3 * b - 4 * a * b ^ 3 + b ^ 4

private theorem rational_doubling_denominator_ne {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    4 * x ^ 3 - 4 * x + 1 ≠ 0 := by
  have hy : y ^ 2 + y = x ^ 3 - x := by
    have v := (Affine.equation_iff ..).mp h.1
    norm_num [W, model, WeierstrassCurve.baseChange] at v
    linarith
  have hne : 2 * y + 1 ≠ 0 := by
    intro hz
    apply not_vertical h
    simp [Affine.negY, W, WeierstrassCurve.baseChange, model]
    linarith
  rw [show 4 * x ^ 3 - 4 * x + 1 = (2 * y + 1) ^ 2 by nlinarith]
  exact pow_ne_zero _ hne

private theorem xRep_double {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    let A := doublingNumerator x.num x.den
    let B := doublingDenominator x.num x.den
    (B : ℚ) ≠ 0 ∧ (Point.some x y h + .some x y h).xRep =
      (B : ℚ)⁻¹ • ((↑) ∘ ![A, B] : Fin 2 → ℚ) := by
  let a : ℤ := x.num
  let b : ℤ := x.den
  let A := doublingNumerator a b
  let B := doublingDenominator a b
  have hb : (b : ℚ) ≠ 0 := by simp [b]
  have hx : x = (a : ℚ) / (b : ℚ) := by simpa [a, b] using x.num_div_den.symm
  have hB : (B : ℚ) = (4 * x ^ 3 - 4 * x + 1) * (b : ℚ) ^ 4 := by
    push_cast [B, doublingDenominator]
    rw [hx]
    field_simp
  have hden := rational_doubling_denominator_ne h
  have hnB : (B : ℚ) ≠ 0 := hB.symm ▸ mul_ne_zero hden (pow_ne_zero _ hb)
  have hA : (A : ℚ) = (x ^ 4 + 2 * x ^ 2 - 2 * x + 1) * (b : ℚ) ^ 4 := by
    push_cast [A, doublingNumerator]
    rw [hx]
    field_simp
  have hrep : ((Point.some x y h) + .some x y h).xRep =
      (B : ℚ)⁻¹ • ((↑) ∘ ![A, B] : Fin 2 → ℚ) := by
    rw [Point.xRep_add_self_of_Y_ne h (not_vertical h)]
    have ha : W.b₄ = -2 := by decide +kernel
    have hbb : W.b₂ = 0 := by decide +kernel
    have hc : W.b₆ = 1 := by decide +kernel
    have hd : W.b₈ = -1 := by decide +kernel
    simp only [ha, hbb, hc, hd]
    ext i
    fin_cases i
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, neg_mul, sub_neg_eq_add, mul_one,
        zero_mul, add_zero, mul_neg, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
        Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      rw [hA, hB]
      field_simp; ring
    · simp [Function.comp_def, hnB]
  exact ⟨hnB, hrep⟩

private theorem abs_doublingCoefficients_le (x : ℚ) :
    let m : ℝ := (max x.num.natAbs x.den : ℕ)
    |(doublingNumerator x.num x.den : ℝ)| ≤ 9 * m ^ 4 ∧
      |(doublingDenominator x.num x.den : ℝ)| ≤ 9 * m ^ 4 := by
  let a : ℤ := x.num
  let b : ℤ := x.den
  let A := doublingNumerator a b
  let B := doublingDenominator a b
  let m : ℝ := (max x.num.natAbs x.den : ℕ)
  have hma : |(a : ℝ)| ≤ m := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    change (x.num.natAbs : ℝ) ≤ ((max x.num.natAbs x.den : ℕ) : ℝ)
    exact_mod_cast le_max_left x.num.natAbs x.den
  have hmb : |(b : ℝ)| ≤ m := by
    rw [show (b : ℝ) = (x.den : ℝ) by simp [b], abs_of_nonneg (by positivity)]
    change (x.den : ℝ) ≤ ((max x.num.natAbs x.den : ℕ) : ℝ)
    exact_mod_cast le_max_right x.num.natAbs x.den
  have habs_sub (u v : ℝ) : |u - v| ≤ |u| + |v| := by
    simpa using abs_sub_le u 0 v
  have hamax : |(A : ℝ)| ≤ 9 * m ^ 4 := by
    calc
      |(A : ℝ)| ≤ |(a : ℝ)| ^ 4 + 2 * |(a : ℝ)| ^ 2 * |(b : ℝ)| ^ 2 +
          2 * |(a : ℝ)| * |(b : ℝ)| ^ 3 + |(b : ℝ)| ^ 4 := by
        push_cast [A, doublingNumerator]
        refine (abs_add_le _ _).trans (add_le_add ?_ (abs_pow _ _).le)
        refine (habs_sub _ _).trans (add_le_add ?_ ?_)
        · exact (abs_add_le _ _).trans (by
            rw [abs_pow, abs_mul, abs_mul, abs_pow, abs_pow]
            norm_num)
        · rw [abs_mul, abs_mul, abs_pow]
          norm_num
      _ ≤ m ^ 4 + 2 * m ^ 2 * m ^ 2 + 2 * m * m ^ 3 + m ^ 4 := by gcongr
      _ ≤ _ := by nlinarith
  have hbmax : |(B : ℝ)| ≤ 9 * m ^ 4 := by
    calc
      |(B : ℝ)| ≤ 4 * |(a : ℝ)| ^ 3 * |(b : ℝ)| +
          4 * |(a : ℝ)| * |(b : ℝ)| ^ 3 + |(b : ℝ)| ^ 4 := by
        push_cast [B, doublingDenominator]
        refine (abs_add_le _ _).trans (add_le_add ?_ (abs_pow _ _).le)
        exact (habs_sub _ _).trans (by
          rw [abs_mul, abs_mul, abs_pow, abs_mul, abs_mul, abs_pow]
          norm_num)
      _ ≤ 4 * m ^ 3 * m + 4 * m * m ^ 3 + m ^ 4 := by gcongr
      _ = _ := by ring
  exact ⟨hamax, hbmax⟩

private theorem logHeight_doublingCoefficients (x : ℚ) :
    logHeight ((↑) ∘ ![doublingNumerator x.num x.den, doublingDenominator x.num x.den]
      : Fin 2 → ℚ) ≤ 4 * Real.log (max x.num.natAbs x.den : ℕ) + 4 := by
  let A := doublingNumerator x.num x.den
  let B := doublingDenominator x.num x.den
  let m : ℝ := (max x.num.natAbs x.den : ℕ)
  have hm : 1 ≤ m := by
    change (1 : ℝ) ≤ ((max x.num.natAbs x.den : ℕ) : ℝ)
    exact_mod_cast (x.pos.trans_le (le_max_right x.num.natAbs x.den))
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hSup : (⨆ i : Fin 2, |(![A, B] : Fin 2 → ℤ) i|) = max |A| |B| := by
    apply eq_of_forall_ge_iff
    intro z
    simp [ciSup_le_iff, Fin.forall_fin_two]
  obtain ⟨hA, hB⟩ := abs_doublingCoefficients_le x
  have hlim : (↑(⨆ i : Fin 2, |(![A, B] : Fin 2 → ℤ) i|) : ℝ) ≤ 9 * m ^ 4 := by
    rw [hSup]
    push_cast
    exact max_le hA hB
  have hnonneg : (0 : ℝ) ≤ ↑(⨆ i : Fin 2, |(![A, B] : Fin 2 → ℤ) i|) := by
    rw [hSup]
    exact_mod_cast (abs_nonneg A).trans (le_max_left |A| |B|)
  change logHeight (((↑) : ℤ → ℚ) ∘ ![A, B]) ≤ 4 * Real.log m + 4
  rcases hnonneg.eq_or_lt with hzero | hpos
  · have h := Rat.logHeight_le_max_abs (![A, B] : Fin 2 → ℤ)
    rw [← hzero, Real.log_zero] at h
    linarith [Real.log_nonneg hm]
  have hlog9 : Real.log 9 ≤ 4 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num at *
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    linarith
  refine (Rat.logHeight_le_max_abs _).trans ((Real.log_le_log hpos hlim).trans ?_)
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hmpos.ne'), Real.log_pow]
  change _ ≤ 4 * Real.log m + 4
  norm_num
  linarith


private theorem logHeight_double (P : W.toAffine.Point) :
    (P + P).naiveHeight ≤ 4 * P.naiveHeight + 4 := by
  cases P with
  | zero => simp [← Point.zero_def]
  | some x y h =>
    obtain ⟨hnB, hrep⟩ := xRep_double h
    rw [Point.naiveHeight_eq_logHeight, hrep, logHeight_smul_eq_logHeight _ (inv_ne_zero hnB),
      Point.naiveHeight_eq_logHeight₁, Point.xRep_some]
    simp only [Matrix.cons_val_zero, Rat.logHeight₁_eq_log_max]
    exact logHeight_doublingCoefficients x

private theorem canonical_le (P : W.toAffine.Point) :
    P.canonicalHeight ≤ P.naiveHeight + 4 / 3 := by
  have hbound (n : ℕ) :
      ((2 ^ n : ℕ) • P).naiveHeight ≤ 4 ^ n * (P.naiveHeight + 4 / 3) - 4 / 3 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have step : ((2 ^ (n + 1) : ℕ) • P) = 2 • ((2 ^ n : ℕ) • P) := by
        rw [smul_smul, pow_succ']
      rw [step, two_nsmul, pow_succ' (4 : ℝ)]
      linarith only [ih, logHeight_double ((2 ^ n : ℕ) • P)]
  apply le_of_tendsto P.tendsto_naiveHeight_two_pow_nsmul_div_four_pow
  exact .of_forall fun n => (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)).mpr
    (by linarith only [hbound n])

/-- The single affine point in the LMFDB generator list. -/
def source (_ : Fin 1) : W.toAffine.Point :=
  .mk (x := 0) (y := 0) (by
    rw [Affine.equation_iff]
    norm_num [W, model, WeierstrassCurve.baseChange])

private theorem naiveEight :
    ((8 : ℕ) • source 0).naiveHeight = Real.log 25 := by
  rw [Point.naiveHeight_eq_logHeight₁]
  have hx : (((8 : ℕ) • source 0).xRep 0) = 21 / 25 := by
    decide +kernel
  rw [hx]
  have hr : max ((21 / 25 : ℚ).num.natAbs) (21 / 25 : ℚ).den = 25 := by decide +kernel
  simp [Rat.logHeight₁_eq_log_max, hr]

private theorem heightUpper :
    (source 0).canonicalHeight ≤ 19 / 192 := by
  have hlog25 : Real.log 25 ≤ 5 := by
    calc
      Real.log 25 ≤ Real.log (2 ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
      _ ≤ 5 := by
        rw [Real.log_pow]
        norm_num
        have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
  have h := canonical_le ((8 : ℕ) • source 0)
  rw [Point.canonicalHeight_nsmul, naiveEight] at h
  norm_num at h
  linarith

/-- A checked enclosure for the height of the reported point. -/
def heights :
    Σ points : (Σ n : ℕ, Fin n → W.toAffine.Point), CanonicalHeightFacts points.2 :=
  ⟨⟨1, source⟩, {
    reported := fun _ => 0.051111408239968840235886099757
    error := fun _ => 3 / 50
    error_nonneg := by norm_num
    within_error := by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [abs_le]
      constructor
      · norm_num
        linarith [(source 0).canonicalHeight_nonneg]
      · norm_num
        linarith [heightUpper] }⟩

certify_ec Height from_json_string
  r#"{"ainvs":[0,0,1,-1,0],"discriminant":37,"gens":[[0,0,1]],"ngens":1,
    "heights":[{"__RealLiteral__":0,"data":"0.051111408239968840235886099757","prec":97}],
    "heights_evidence":{"errors":["3/50"]}}"#
  with_proofs ({ canonicalHeights := some heights } : IntegralCurveProofs model)

end Height37
