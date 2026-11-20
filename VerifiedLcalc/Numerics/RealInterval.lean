module
public import VerifiedLcalc.Numerics.RealIntervalCore
public import VerifiedLcalc.Numerics.RationalExp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
@[expose] public section
namespace VerifiedLcalc.Numerics

def RealInterval.Contains (i : RealInterval) (x : ℝ) : Prop := x ∈ Set.Icc (i.1 : ℝ) (i.2 : ℝ)

theorem roundInterval_sound (bits : Nat) (i : RealInterval) (x : ℝ) (hi : i.Contains x) :
    (roundInterval bits i).Contains x := by
  have hl : (((i.1.toDyadic bits).toRat : Rat) : ℝ) ≤ (i.1 : ℝ) := by
    exact_mod_cast Rat.toRat_toDyadic_le (x := i.1) (prec := bits)
  have hu : ((((-i.2).toDyadic bits).toRat : Rat) : ℝ) ≤ -(i.2 : ℝ) := by
    exact_mod_cast Rat.toRat_toDyadic_le (x := -i.2) (prec := bits)
  exact ⟨hl.trans hi.1, by change x ≤ ((-(((-i.2).toDyadic bits).toRat) : Rat) : ℝ); push_cast; linarith [hi.2]⟩

theorem intervalAdd_sound (i j : RealInterval) (x y : ℝ)
    (hx : i.Contains x) (hy : j.Contains y) : (intervalAdd i j).Contains (x+y) := by
  exact ⟨by simpa [intervalAdd] using add_le_add hx.1 hy.1,
    by simpa [intervalAdd] using add_le_add hx.2 hy.2⟩

private theorem mul_bounds (a b c d x y : ℝ) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have low (z : ℝ) (hz : z = a*c ∨ z = a*d ∨ z = b*c ∨ z = b*d) :
      min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ z := by
    rcases hz with rfl | rfl | rfl | rfl <;> simp [min_le_iff]
  have high (z : ℝ) (hz : z = a*c ∨ z = a*d ∨ z = b*c ∨ z = b*d) :
      z ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
    rcases hz with rfl | rfl | rfl | rfl <;> simp [le_max_iff]
  constructor
  · by_cases h : 0 ≤ x
    · have hh := mul_le_mul_of_nonneg_left hy.1 h
      by_cases hc : 0 ≤ c
      · exact (low _ (by tauto)).trans ((mul_le_mul_of_nonneg_right hx.1 hc).trans hh)
      · exact (low _ (by tauto)).trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hc)).trans hh)
    · have hh := mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge h)
      by_cases hd : 0 ≤ d
      · exact (low _ (by tauto)).trans ((mul_le_mul_of_nonneg_right hx.1 hd).trans hh)
      · exact (low _ (by tauto)).trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hd)).trans hh)
  · by_cases h : 0 ≤ x
    · have hh := mul_le_mul_of_nonneg_left hy.2 h
      by_cases hd : 0 ≤ d
      · exact hh.trans ((mul_le_mul_of_nonneg_right hx.2 hd).trans (high _ (by tauto)))
      · exact hh.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd)).trans (high _ (by tauto)))
    · have hh := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge h)
      by_cases hc : 0 ≤ c
      · exact hh.trans ((mul_le_mul_of_nonneg_right hx.2 hc).trans (high _ (by tauto)))
      · exact hh.trans ((mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc)).trans (high _ (by tauto)))

theorem intervalMul_sound (i j : RealInterval) (x y : ℝ)
    (hx : i.Contains x) (hy : j.Contains y) : (intervalMul i j).Contains (x*y) := by
  obtain ⟨hxl, hxh⟩ := hx
  obtain ⟨hyl, hyh⟩ := hy
  unfold intervalMul
  split
  · next hi =>
    have hi' : (0 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast hi
    have hx0 : 0 ≤ x := hi'.trans hxl
    split
    · next hj =>
      have hj' : (0 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hj
      simpa [RealInterval.Contains] using
        And.intro (mul_le_mul hxl hyl hj' hx0)
          (mul_le_mul hxh hyh (hj'.trans hyl) (hx0.trans hxh))
    · split
      · next hj =>
        have hj' : (j.2 : ℝ) ≤ 0 := by exact_mod_cast hj
        constructor <;> simp only [Rat.cast_mul]
        · exact (mul_le_mul_of_nonpos_right hxh (hyl.trans (hyh.trans hj'))).trans
            (mul_le_mul_of_nonneg_left hyl hx0)
        · exact (mul_le_mul_of_nonneg_left hyh hx0).trans
            (mul_le_mul_of_nonpos_right hxl hj')
      · have hy0 : (j.1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge ‹¬ 0 ≤ j.1›)
        have hy1 : (0 : ℝ) ≤ (j.2 : ℝ) := by exact_mod_cast (le_of_not_ge ‹¬ j.2 ≤ 0›)
        constructor <;> simp only [Rat.cast_mul]
        · exact (mul_le_mul_of_nonpos_right hxh hy0).trans
            (mul_le_mul_of_nonneg_left hyl hx0)
        · exact (mul_le_mul_of_nonneg_left hyh hx0).trans
            (mul_le_mul_of_nonneg_right hxh hy1)
  · split
    · next hi =>
      have hi' : (i.2 : ℝ) ≤ 0 := by exact_mod_cast hi
      have hx0 : x ≤ 0 := hxh.trans hi'
      split
      · next hj =>
        have hj' : (0 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hj
        constructor <;> simp only [Rat.cast_mul]
        · exact (mul_le_mul_of_nonpos_left hyh (hxl.trans hx0)).trans
            (mul_le_mul_of_nonneg_right hxl (hj'.trans hyl))
        · exact (mul_le_mul_of_nonpos_left hyl hx0).trans
            (mul_le_mul_of_nonneg_right hxh hj')
      · split
        · next hj =>
          have hj' : (j.2 : ℝ) ≤ 0 := by exact_mod_cast hj
          constructor <;> simp only [Rat.cast_mul]
          · exact (mul_le_mul_of_nonpos_left hyh hi').trans
              (mul_le_mul_of_nonpos_right hxh (hyh.trans hj'))
          · exact (mul_le_mul_of_nonpos_right hxl (hyh.trans hj')).trans
              (mul_le_mul_of_nonpos_left hyl (hxl.trans hx0))
        · have hy0 : (j.1 : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge ‹¬ 0 ≤ j.1›)
          have hy1 : (0 : ℝ) ≤ (j.2 : ℝ) := by exact_mod_cast (le_of_not_ge ‹¬ j.2 ≤ 0›)
          constructor <;> simp only [Rat.cast_mul]
          · exact (mul_le_mul_of_nonneg_right hxl hy1).trans
              (mul_le_mul_of_nonpos_left hyh hx0)
          · exact (mul_le_mul_of_nonpos_left hyl hx0).trans
              (mul_le_mul_of_nonpos_right hxl hy0)
    · simpa [RealInterval.Contains] using mul_bounds _ _ _ _ _ _ ⟨hxl, hxh⟩ ⟨hyl, hyh⟩

def polynomialValue (q : ℝ) : List Int → ℝ
  | [] => 0
  | a :: cs => a+q*polynomialValue q cs

theorem polynomialBounds_sound (bits : Nat) (i : RealInterval) (q : ℝ) (hq : i.Contains q)
    (cs : List Int) : (polynomialBounds bits i cs).Contains (polynomialValue q cs) := by
  induction cs with
  | nil => simp [polynomialBounds, polynomialValue, RealInterval.Contains]
  | cons a cs ih =>
    exact roundInterval_sound bits _ _ (intervalAdd_sound _ _ _ _
      ⟨by simp,by simp⟩ (intervalMul_sound _ _ _ _ hq ih))

private theorem sum_map_range (f : Nat → ℝ) (n : Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]

/-- Finite successful interval collection preserves every supplied enclosure. -/
theorem mapM_sumIntervalBounds_sound {A : Type} (xs : List A) (bounds : A → Option RealInterval)
    (value : A → ℝ) (bits : Nat) (is : List RealInterval)
    (he : xs.mapM bounds = some is)
    (hb : ∀ x ∈ xs, ∀ i, bounds x = some i → i.Contains (value x)) :
    (sumIntervalBounds bits is).Contains ((xs.map value).sum) := by
  induction xs generalizing is with
  | nil => simp at he; subst is; simp [sumIntervalBounds, RealInterval.Contains]
  | cons x xs ih =>
    cases hx : bounds x with
    | none => simp [hx] at he
    | some i =>
      cases hs : xs.mapM bounds with
      | none => simp [hx,hs] at he
      | some rest =>
        simp [hx,hs] at he
        subst is
        have hfirst := hb x (by simp) i hx
        have hrest := ih rest hs (fun x hm => hb x (List.mem_cons_of_mem _ hm))
        exact roundInterval_sound bits _ _ (intervalAdd_sound _ _ _ _ hfirst hrest)

/-- Certified logarithms from mathlib's explicit atanh-series remainder bound. -/
theorem logBounds_sound (t : Rat) (terms bits : Nat) (ht : 1 ≤ t) :
    (logBounds t terms bits).Contains (Real.log (t : ℝ)) := by
  let y : ℝ := ((t : ℝ)-1)/((t : ℝ)+1)
  have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
  have hy1 : y < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have he : (1+y)/(1-y) = (t : ℝ) := by
    dsimp [y]
    field_simp <;> ring
  have hl := Real.sum_range_le_log_div hy0 hy1 terms
  have hu := Real.log_div_le_sum_range_add hy0 hy1 terms
  rw [he] at hl hu
  unfold logBounds
  apply roundInterval_sound
  constructor
  · change ((2*((List.range terms).map _).sum : Rat) : ℝ) ≤ _
    push_cast
    simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_add, Rat.cast_mul, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat]
    rw [sum_map_range]
    change 2*(∑ k ∈ Finset.range terms, y^(2*k+1)/(2*(k : ℝ)+1)) ≤ _
    linarith
  · change _ ≤ ((2*((List.range terms).map _).sum + _ : Rat) : ℝ)
    push_cast
    simp only [List.map_map, Function.comp_def, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_add, Rat.cast_mul, Rat.cast_one, Rat.cast_natCast, Rat.cast_ofNat]
    rw [sum_map_range]
    change _ ≤ 2*(∑ k ∈ Finset.range terms, y^(2*k+1)/(2*(k : ℝ)+1)) + 2*y^(2*terms+1)/(1-y^2)
    convert mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
end VerifiedLcalc.Numerics
