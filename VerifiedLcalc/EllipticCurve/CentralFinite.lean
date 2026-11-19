module

public import VerifiedLcalc.EllipticCurve.CentralCore
public import VerifiedLcalc.Numerics.RationalExp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Numerics

theorem piBounds_correct : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ) := by
  constructor
  · have := Real.pi_gt_d20
    norm_num [piLower] at *
    exact le_of_lt this
  · have := Real.pi_lt_d20
    norm_num [piUpper] at *
    exact le_of_lt this

/-- The square-root and pi approximations both contribute to the enclosing
interval for the actual elliptic exponential scale. -/
theorem alphaBounds_correct (conductor bits : Nat) (hn : 0 < conductor) :
    ((alphaBounds conductor bits).1 : ℝ) ≤ 2 * Real.pi / Real.sqrt conductor ∧
      2 * Real.pi / Real.sqrt conductor ≤ ((alphaBounds conductor bits).2 : ℝ) := by
  let scale := 2 ^ bits
  let root := Nat.sqrt (conductor * scale ^ 2)
  have hs : (0 : ℝ) < (scale : ℝ) := by dsimp [scale]; positivity
  have hn' : (0 : ℝ) < (conductor : ℝ) := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (conductor : ℝ) := Real.sqrt_pos.mpr hn'
  have hsq := Real.sq_sqrt (le_of_lt hn')
  have hlo : (root : ℝ) ^ 2 ≤ (conductor : ℝ) * (scale : ℝ) ^ 2 := by
    exact_mod_cast Nat.sqrt_le' (conductor * scale ^ 2)
  have hhi : (conductor : ℝ) * (scale : ℝ) ^ 2 < ((root : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (conductor * scale ^ 2)
  have hsroot : (root : ℝ) ≤ Real.sqrt conductor * (scale : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow, hsq] using hlo
  have hrootS : Real.sqrt conductor * (scale : ℝ) ≤ (root : ℝ) + 1 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow, hsq] using hhi.le
  have rootPos : (0 : ℝ) < (root : ℝ) := by
    have : 0 < root := Nat.sqrt_pos.mpr (by dsimp [scale]; positivity)
    exact_mod_cast this
  have rootSuccPos : (0 : ℝ) < (root : ℝ) + 1 := by positivity
  have hp := piBounds_correct
  have hpiLo : (0 : ℝ) ≤ (piLower : ℝ) := by norm_num [piLower]
  have hpiHi : (0 : ℝ) ≤ (piUpper : ℝ) := by norm_num [piUpper]
  change (((2 * piLower * scale / (root + 1 : Nat) : Rat) : ℝ) ≤ _ ∧
    _ ≤ ((2 * piUpper * scale / root : Rat) : ℝ))
  push_cast
  constructor
  · apply (div_le_div_iff₀ rootSuccPos hr).mpr
    have h1 := mul_le_mul_of_nonneg_right hp.1 (le_of_lt (mul_pos hs hr))
    have h2 := mul_le_mul_of_nonneg_left hrootS (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith
  · apply (div_le_div_iff₀ hr rootPos).mpr
    have h1 := mul_le_mul_of_nonneg_left hsroot (show 0 ≤ 2 * Real.pi by positivity)
    have h2 := mul_le_mul_of_nonneg_right hp.2 (le_of_lt (mul_pos hs hr))
    nlinarith

noncomputable def centralFiniteValue (coefficients : List Int) (rootNumber : Int)
    (alpha : ℝ) : ℝ :=
  (coefficients.zipIdx.map fun (a, j) =>
    ((1 + rootNumber : Int) : ℝ) * (a : ℝ) / (j + 1 : Nat) *
      Real.exp (-alpha * (j + 1 : Nat))).sum

/-- The list evaluator's indexing agrees with the mathematical prefix sum. -/
theorem centralFiniteValue_map_range (a : ℕ → ℤ) (limit : ℕ) (w : ℤ) (alpha : ℝ) :
    centralFiniteValue ((List.range limit).map (fun j => a (j + 1))) w alpha =
      ∑ j ∈ Finset.range limit, ((1 + w : ℤ) : ℝ) * (a (j + 1) : ℝ) /
        (j + 1 : ℕ) * Real.exp (-alpha * (j + 1 : ℕ)) := by
  have hz : ((List.range limit).map (fun j => a (j + 1))).zipIdx =
      (List.range limit).map (fun j => (a (j + 1), j)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [centralFiniteValue, hz, List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  have hr : (List.range limit).toFinset = Finset.range limit := by
    ext j
    simp
  simp [hr]

theorem indexedExpSumBounds_correct (terms : List (Nat × RationalExpTerm))
    (prec : Nat) (alpha : ℝ)
    (ha : ∀ t ∈ terms, (t.2.argumentLo : ℝ) ≤ -alpha * t.1 ∧
      -alpha * t.1 ≤ (t.2.argumentHi : ℝ)) :
    ((rationalExpSumBounds prec (terms.map Prod.snd)).1 : ℝ) ≤
      (terms.map fun t => (t.2.coefficient : ℝ) * Real.exp (-alpha * t.1)).sum ∧
    (terms.map fun t => (t.2.coefficient : ℝ) * Real.exp (-alpha * t.1)).sum ≤
      ((rationalExpSumBounds prec (terms.map Prod.snd)).2 : ℝ) := by
  induction terms with
  | nil => simp [rationalExpSumBounds]
  | cons t ts ih =>
    have hh := rationalWeightedBounds_correct t.2 prec (-alpha * t.1) (ha t (by simp))
    have ht := ih (fun t hm => ha t (by simp [hm]))
    simpa only [List.map_cons, rationalExpSumBounds, List.sum_cons, Rat.cast_add] using
      And.intro (add_le_add hh.1 ht.1) (add_le_add hh.2 ht.2)

theorem centralFiniteBounds_correct (coefficients : List Int) (rootNumber : Int)
    (alphaLo alphaHi : Rat) (prec : Nat) (alpha : ℝ)
    (ha : (alphaLo : ℝ) ≤ alpha ∧ alpha ≤ (alphaHi : ℝ)) :
    ((rationalExpSumBounds prec
      ((centralTerms coefficients rootNumber alphaLo alphaHi).map Prod.snd)).1 : ℝ) ≤
      centralFiniteValue coefficients rootNumber alpha ∧
    centralFiniteValue coefficients rootNumber alpha ≤
      ((rationalExpSumBounds prec
        ((centralTerms coefficients rootNumber alphaLo alphaHi).map Prod.snd)).2 : ℝ) := by
  have h := indexedExpSumBounds_correct
    (centralTerms coefficients rootNumber alphaLo alphaHi) prec alpha (by
      intro t ht
      obtain ⟨⟨a, j⟩, _, rfl⟩ := List.mem_map.mp ht
      change ((-alphaHi * (j + 1 : Nat) : Rat) : ℝ) ≤ -alpha * (j + 1 : Nat) ∧
        -alpha * (j + 1 : Nat) ≤ ((-alphaLo * (j + 1 : Nat) : Rat) : ℝ)
      push_cast
      constructor
      · simpa only [neg_mul] using
          neg_le_neg (mul_le_mul_of_nonneg_right ha.2 (show 0 ≤ (j : ℝ) + 1 by positivity))
      · simpa only [neg_mul] using
          neg_le_neg (mul_le_mul_of_nonneg_right ha.1 (show 0 ≤ (j : ℝ) + 1 by positivity)))
  simpa [centralTerms, centralFiniteValue, List.map_map, Function.comp_def] using h

end VerifiedLcalc.EllipticCurve
