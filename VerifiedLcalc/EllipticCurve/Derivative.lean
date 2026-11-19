module
public import VerifiedLcalc.Numerics.DerivativeQuadrature
public import VerifiedLcalc.EllipticCurve.CentralFinite
@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open Numerics MeasureTheory Set

theorem derivativeInfiniteTail_correct (al : Rat) (bits cutoff : Nat) (tail : Rat)
    (h : derivativeInfiniteTail al bits cutoff = some tail) :
    let q := (rationalExpBounds (-al*cutoff) (-al*cutoff) bits).2
    0 < al ∧ 1 ≤ cutoff ∧ 2 ≤ al*cutoff ∧ 0 ≤ q ∧ 8*q < 1 ∧
      tail = 2*cutoff/al*q/(1-8*q) := by
  unfold derivativeInfiniteTail at h
  dsimp only at h ⊢
  split at h
  · next hc => cases h; exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,rfl⟩
  · simp at h

/-- Complete enclosure of the actual logarithmic Mellin integral, including
both the Fourier truncation inside every cell and the infinite integration tail. -/
theorem derivativePayload_contains (r : DerivativeResult) (hr : DerivativePayloadCorrect r)
    (a : Nat → Int) (f : ℝ → ℝ)
    (hc : r.coefficients = (List.range r.termLimit).map (fun j => a (j+1)))
    (hb : ∀ j, |(a (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3)
    (hf : ∀ t, 0 < t → HasSum
      (fun j => (a (j+1) : ℝ)*Real.exp (-(2*Real.pi/Real.sqrt r.conductor)*t)^(j+1)) (f t))
    (hi : IntegrableOn (fun t => Real.log t*f t) (Ioi 0)) :
    r.box.Contains (Complex.ofReal (∫ t : ℝ in Ioi 1, Real.log t*f t)) := by
  obtain ⟨hn,hs,hcut,_,hal,hah,htail,hfinite,hbox⟩ := hr
  let alpha := 2*Real.pi/Real.sqrt r.conductor
  have ha := alphaBounds_correct r.conductor r.policy.precisionBits hn
  rw [← hal,← hah] at ha
  have ha0 : 0 < alpha := div_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hclen : r.coefficients.length = r.termLimit := by rw [hc]; simp
  have hc' : r.coefficients = (List.range r.coefficients.length).map (fun j => a (j+1)) := by
    rw [hclen]; exact hc
  have hfinite' := derivativeFiniteBounds_sound a r.coefficients r.alphaLo r.alphaHi
    r.policy.precisionBits r.stepsPerUnit r.cutoff r.finite alpha f hs ha ha0 hc' hb hf hi hcut.le hfinite
  obtain ⟨hal0,hT,hstart,hQ0,hQ,htailval⟩ := derivativeInfiniteTail_correct _ _ _ _ htail
  let Q : Rat := (rationalExpBounds (-r.alphaLo*r.cutoff) (-r.alphaLo*r.cutoff) r.policy.precisionBits).2
  have hal0' : (0 : ℝ) < (r.alphaLo : ℝ) := by exact_mod_cast hal0
  have hT' : (1 : ℝ) ≤ (r.cutoff : ℝ) := by exact_mod_cast hT
  have hstart' : (2 : ℝ) ≤ (r.alphaLo : ℝ)*(r.cutoff : ℝ) := by exact_mod_cast hstart
  have hQ' : (8 : ℝ)*(Q : ℝ) < 1 := by exact_mod_cast hQ
  have hqexp : Real.exp (-alpha*(r.cutoff : ℝ)) ≤ (Q : ℝ) := by
    have h := (rationalExpBounds_correct (-r.alphaLo*r.cutoff) (-r.alphaLo*r.cutoff)
      r.policy.precisionBits (-(r.alphaLo : ℝ)*r.cutoff) (by simp) (by simp)).2
    apply le_trans _ h
    apply Real.exp_le_exp.mpr
    dsimp [alpha]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.1) (show (0 : ℝ) ≤ r.cutoff by positivity)]
  have ht := derivative_tail_error a f alpha r.alphaLo r.cutoff Q hal0' ha.1 hT' hstart'
    hqexp hQ' hf hb (hi.mono_set (Ioi_subset_Ioi (by positivity)))
  have htv : (r.tail : ℝ) = 2*r.cutoff/(r.alphaLo : ℝ)*(Q : ℝ)/(1-8*(Q : ℝ)) := by
    rw [htailval]
    push_cast
    rfl
  rw [← htv] at ht
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))) hT'
  have herror : |(∫ t : ℝ in Ioi 1, Real.log t*f t) -
      (∫ t in (1 : ℝ)..(r.cutoff : ℝ), Real.log t*f t)| ≤ (r.tail : ℝ) := by
    have he : (∫ t : ℝ in Ioi 1, Real.log t*f t) -
        (∫ t in (1 : ℝ)..(r.cutoff : ℝ), Real.log t*f t) =
        (∫ t : ℝ in Ioi (r.cutoff : ℝ), Real.log t*f t) := by linarith [hsplit]
    rw [he]; exact ht
  rw [hbox]
  simp only [Box.Contains, Complex.ofReal_re, Complex.ofReal_im]
  constructor
  · change (((r.finite.1-r.tail : Rat) : ℝ) ≤ _ ∧ _ ≤ ((r.finite.2+r.tail : Rat) : ℝ))
    push_cast
    have he := abs_le.mp herror
    constructor <;> linarith [hfinite'.1,hfinite'.2,he.1,he.2]
  · simp [Set.mem_Icc]
end VerifiedLcalc.EllipticCurve
