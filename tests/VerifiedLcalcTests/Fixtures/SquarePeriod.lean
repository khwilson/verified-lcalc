/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import TauCeti.Algebra.Module.ZLattice.Complex
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Area and both height enclosures on the square-lattice curve 32.a3 -/

namespace VerifiedLcalcTests.SquarePeriod

open VerifiedLcalc WeierstrassCurve

/-- The integral equation for 32.a3. -/
public abbrev squareCurve : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 0⟩

public instance : (squareCurve.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

open scoped Real Pointwise
open ComplexConjugate

-- A rescaling of the square lattice matches the invariants of the 32.a3 equation.
-- The q-expansion of E₄ at i gives a rational bound with a geometric tail.
private abbrev L := UpperHalfPlane.I.periodPair
private noncomputable abbrev W : WeierstrassCurve ℂ :=
  (squareCurve.baseChange ℚ).map (Rat.castHom ℂ)
private theorem square_area_sq :
    ZLattice.covolume W.periodLattice ^ 2 = ‖L.g₂ / 4‖ := by
  have h₂ : L.g₂ ≠ 0 := by
    rw [UpperHalfPlane.g₂_periodPair]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) (by norm_num))
      TauCeti.ModularForm.E₄_I_ne_zero
  have h₃ : L.g₃ = 0 := by simp [UpperHalfPlane.g₃_periodPair]
  obtain ⟨c, h⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ / 4) (show 0 < 4 by decide)
  have hc : c ≠ 0 := by
    rintro rfl
    exact h₂ (by simpa using h.symm)
  let u := Units.mk0 c hc
  have h₄ : (u • L).g₂ = 4 := by
    rw [PeriodPair.g₂_smul]
    change L.g₂ / c ^ 4 = 4
    rw [h]
    field_simp
  have h₆ : (u • L).g₃ = 0 := by simp [PeriodPair.g₃_smul, h₃]
  have hW : (u • L).weierstrassCurve = W := by
    ext <;> norm_num [W, WeierstrassCurve.baseChange, WeierstrassCurve.map, h₄, h₆]
  have hLat : W.periodLattice = (u • L).lattice := WeierstrassCurve.periodLattice_eq_iff.mpr
    ⟨1, rfl, (one_smul _ _).trans hW⟩
  rw [hLat, ZLattice.covolume_eq_abs_im _ (u • L).latticeBasis]
  simp only [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one, PeriodPair.smul_ω₁,
    PeriodPair.smul_ω₂, UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.periodPair_ω₂,
    UpperHalfPlane.coe_I, mul_one, map_mul, Complex.conj_I]
  change |((conj c * -Complex.I) * c).im| ^ 2 = _
  have hz : (conj c * -Complex.I) * c = -(‖c‖ ^ 2 : ℝ) * Complex.I := by
    rw [show (conj c * -Complex.I) * c = -(conj c * c) * Complex.I by ring, Complex.conj_mul']
    push_cast
    rfl
  rw [hz, ← h, norm_pow]
  simp [Complex.mul_im, -Complex.ofReal_pow]
  ring

open ArithmeticFunction
open scoped ArithmeticFunction.sigma BigOperators

private theorem sigma3_pow (n : ℕ) : (σ 3 (n + 1) : ℝ) ≤ 16 ^ n := by
  have h : n + 1 ≤ 2 ^ n := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [pow_succ]
      omega
  exact_mod_cast calc
    σ 3 (n + 1) ≤ (n + 1) ^ 4 := sigma_le_pow_succ 3 _
    _ ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left h _
    _ = 16 ^ n := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num

set_option maxHeartbeats 700000 in
private theorem sigma3_geometric_bound {q : ℝ} (hq : 0 ≤ q) (hmax : q ≤ 1 / 500) :
    (∑' n : ℕ, (σ 3 n : ℝ) * q ^ n) ≤ 1 / 484 := by
  have hle : ∀ n : ℕ, (σ 3 (n + 1) : ℝ) * q ^ (n + 1) ≤ q * (16 * q) ^ n := by
    intro n
    calc
      _ ≤ 16 ^ n * q ^ (n + 1) := mul_le_mul_of_nonneg_right (sigma3_pow n) (by positivity)
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hlt : 16 * q < 1 := by linarith
  have hgeom := summable_geometric_of_lt_one (show 0 ≤ 16 * q by positivity) hlt
  have hsum : Summable (fun n : ℕ => (σ 3 (n + 1) : ℝ) * q ^ (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _)) hle 
      (hgeom.mul_left q)
  have hall : Summable (fun n : ℕ => (σ 3 n : ℝ) * q ^ n) := (summable_nat_add_iff 1).mp hsum
  rw [← hall.sum_add_tsum_nat_add 1]
  simp only [Finset.range_one, Finset.sum_singleton, ArithmeticFunction.map_zero, Nat.cast_zero,
    zero_mul, zero_add]
  calc
    _ ≤ ∑' n : ℕ, q * (16 * q) ^ n := hsum.tsum_le_tsum hle (hgeom.mul_left q)
    _ = q * (1 - 16 * q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hlt]
    _ ≤ _ := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < 1 - 16 * q)]
      linarith

private theorem exp_neg_bound : Real.exp (-(2 * Real.pi)) ≤ 1 / 500 := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  calc
    (500 : ℝ) ≤ ∑ i ∈ Finset.range 13, (25 / 4 : ℝ) ^ i / i.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (25 / 4) := Real.sum_le_exp_of_nonneg (by norm_num) _
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d2])

open scoped Real in
private theorem E4_I_size : ∃ e : ℝ, ModularForm.E₄ UpperHalfPlane.I = (e : ℂ) ∧
    1 ≤ e ∧ e ≤ 3 / 2 := by
  let q := Real.exp (-(2 * Real.pi))
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hmax : q ≤ 1 / 500 := exp_neg_bound
  have hn : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq]; linarith
  let s := TauCeti.divisorSumAt 3 q
  have slo : 0 ≤ s := by
    simp only [s, TauCeti.divisorSumAt_def, Int.cast_natCast]
    exact tsum_nonneg (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq n))
  have shi : s ≤ 1 / 484 := by
    simpa only [s, TauCeti.divisorSumAt_def, Int.cast_natCast] using sigma3_geometric_bound hq hmax
  refine ⟨1 + 240 * s, ?_, by linarith, by linarith⟩
  rw [TauCeti.ModularForm.E₄_apply_eq_divisorSumAt]
  have harg : Complex.exp (2 * Real.pi * Complex.I * (UpperHalfPlane.I : ℂ)) = (q : ℂ) := by
    rw [UpperHalfPlane.coe_I, mul_assoc, Complex.I_mul_I, mul_neg_one]
    simp [q]
  rw [harg]
  have hm := TauCeti.map_divisorSumAt Complex.ofRealHom Complex.continuous_ofReal 3 q hn
  change (s : ℂ) = TauCeti.divisorSumAt 3 (q : ℂ) at hm
  rw [← hm]
  push_cast
  rfl

open scoped Real in
private theorem area_bounds_of_sq (a : ℝ) (hn : 0 ≤ a)
    (h : a ^ 2 = ‖UpperHalfPlane.I.periodPair.g₂ / 4‖) : 5.6 ≤ a ∧ a ≤ 7.1 := by
  obtain ⟨e,he,elo,ehi⟩ := E4_I_size
  rw [UpperHalfPlane.g₂_periodPair, he] at h
  have hc : 4 * (Real.pi : ℂ)^4 / 3 * (e : ℂ) / 4 = ((Real.pi ^ 4 / 3 * e : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
  have lo : 3.14 ^ 4 * (1:ℝ) ≤ Real.pi ^ 4 * e := by gcongr; exact Real.pi_gt_d2.le
  have hi : Real.pi ^ 4 * e ≤ 3.15 ^ 4 * (3 / 2:ℝ) := by gcongr; linarith [Real.pi_lt_d2]
  constructor <;> nlinarith

/-- The square period lattice gives a coarse rigorous area interval for 32.a3. -/
public theorem squareAreaBounds :
    5 ≤ complexPeriodArea (squareCurve.baseChange ℚ) ∧
      complexPeriodArea (squareCurve.baseChange ℚ) ≤ 8 := by
  have h := area_bounds_of_sq _ (ZLattice.covolume_pos _ _).le square_area_sq
  change 5 ≤ ZLattice.covolume W.periodLattice ∧ ZLattice.covolume W.periodLattice ≤ 8
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem squareMinimal : IsGlobalMinimal ℤ (squareCurve.baseChange ℚ) := by
  apply IsGlobalMinimal.of_forall_isMinimal
  intro v
  apply isMinimal_baseChange_of_not_pow_twelve_dvd_span_Δ
  intro h
  let p := Submodule.IsPrincipal.generator v.asIdeal
  have hp : Prime p := Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot
  have hspan : Ideal.span {p} = v.asIdeal := Ideal.span_singleton_generator v.asIdeal
  rw [← hspan, Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd] at h
  have hd : squareCurve.Δ.natAbs = 64 := by decide +kernel
  have habs : (p.natAbs ^ 12 : ℕ) ≤ 64 := by
    simpa only [Int.natAbs_pow, hd] using
      Int.natAbs_le_of_dvd_ne_zero h (show squareCurve.Δ ≠ 0 by decide +kernel)
  have hlo := Nat.pow_le_pow_left (Int.prime_iff_natAbs_prime.mp hp).two_le 12
  omega

private theorem logBounds (x : ℝ) (hlo : 5 ≤ x) (hhi : x ≤ 8) :
    1 ≤ Real.log x ∧ Real.log x ≤ 3 := by
  have h₁ := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h₂ := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h₃ := Real.strictMonoOn_log.monotoneOn (show (2 ^ 2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show x ∈ Set.Ioi 0 by
      change 0 < x
      linarith)
    (show (2 ^ 2 : ℝ) ≤ x by
      norm_num
      linarith)
  have h₄ := Real.strictMonoOn_log.monotoneOn
    (show x ∈ Set.Ioi 0 by
      change 0 < x
      linarith)
    (show (2 ^ 3 : ℝ) ∈ Set.Ioi 0 by norm_num) (show x ≤ (2 ^ 3 : ℝ) by
      rw [show (2 ^ 3 : ℝ) = 8 by norm_num]
      exact hhi)
  rw [Real.log_pow] at h₃ h₄
  norm_num at h₁ h₂ h₃ h₄
  constructor <;> linarith

private theorem stableCorrection :
    catalogueStableFaltingsHeight (squareCurve.baseChange ℚ) =
      catalogueFaltingsHeight (squareCurve.baseChange ℚ) - Real.log 2 / 2 := by
  unfold catalogueStableFaltingsHeight
  have hj : (squareCurve.baseChange ℚ).j.den = 1 := by
    rw [WeierstrassCurve.j_eq]
    decide +kernel
  have hd : (squareCurve.baseChange ℚ).Δ = 64 := by decide +kernel
  rw [hj, hd]
  have hlog : Real.log ((1 : ℝ) / |((64 : ℚ) : ℝ)|) = -6 * Real.log 2 := by
    rw [show (1 : ℝ) / |((64 : ℚ) : ℝ)| = ((2 : ℝ) ^ 6)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  rw [Nat.cast_one, hlog]
  ring

/-- Produce enclosures centered on the reported decimals of 32.a3 from bounds
on the square period lattice. -/
@[expose] public def squareAttachment (hlo : 5 ≤ complexPeriodArea (squareCurve.baseChange ℚ))
    (hhi : complexPeriodArea (squareCurve.baseChange ℚ) ≤ 8) :
    IntegralCurveProofs squareCurve where
  periodGeometry := some {
    minimal := by exact squareMinimal
    area := some ⟨68751858180203728274900957798 / 10 ^ 28, ⟨2, by decide⟩, by
      rw [abs_le]
      norm_num
      constructor <;> linarith⟩
    height := some ⟨-96395933563153686354365902258 / 10 ^ 29, ⟨1, by decide⟩, by
      obtain ⟨hl, hu⟩ := logBounds _ hlo hhi
      rw [catalogueFaltingsHeight, abs_le]
      norm_num
      constructor <;> linarith⟩
    stableHeight := some ⟨-13105329259115095182522750833 / 10 ^ 28, ⟨1, by decide⟩, by
      obtain ⟨hl, hu⟩ := logBounds _ hlo hhi
      have h₂ := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      have h₃ := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      rw [stableCorrection, catalogueFaltingsHeight, abs_le]
      norm_num
      constructor <;> linarith⟩ }

/-- The three producer-centered enclosures follow from the proved square-lattice bound. -/
@[expose] public def squareProofs : IntegralCurveProofs squareCurve :=
  squareAttachment squareAreaBounds.1 squareAreaBounds.2

public section

certify_ec Square32 from_json_string
  r#"{"ainvs":[0,0,0,-1,0],"discriminant":64,"area":6.8751858180203728274900957798,
      "area_evidence":{"error":2},
      "faltings_height":-0.96395933563153686354365902258,
      "faltings_height_evidence":{"error":1},
      "stable_faltings_height":-1.3105329259115095182522750833,
      "stable_faltings_height_evidence":{"error":1}}"#
  with_proofs squareProofs

end

end VerifiedLcalcTests.SquarePeriod
