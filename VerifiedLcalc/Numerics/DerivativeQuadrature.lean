module
public import VerifiedLcalc.Numerics.DerivativeTail
@[expose] public section
namespace VerifiedLcalc.Numerics
open MeasureTheory Set

/-- The finite quadrature is the sum of individually checked cell integrals,
with outward rounding after each addition. -/
theorem derivativeFiniteBounds_sound (a : Nat → Int) (cs : List Int) (al ah : Rat)
    (bits steps cutoff : Nat) (out : RealInterval) (alpha : ℝ) (f : ℝ → ℝ)
    (hs : 0 < steps)
    (ha : (al : ℝ) ≤ alpha ∧ alpha ≤ (ah : ℝ)) (ha0 : 0 < alpha)
    (hc : cs = (List.range cs.length).map (fun j => a (j+1)))
    (hb : ∀ j, |(a (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3)
    (hf : ∀ t, 0 < t → HasSum (fun j => (a (j+1) : ℝ)*Real.exp (-alpha*t)^(j+1)) (f t))
    (hi : IntegrableOn (fun t => Real.log t*f t) (Ioi 0))
    (hcut : 1 ≤ cutoff)
    (he : EllipticCurve.derivativeFiniteBounds cs al ah bits steps cutoff = some out) :
    out.Contains (∫ t in (1 : ℝ)..(cutoff : ℝ), Real.log t*f t) := by
  let point : Nat → ℝ := fun j => 1+(j : ℝ)/steps
  have hsp : (0 : ℝ) < (steps : ℝ) := by exact_mod_cast hs
  have hp1 (j : Nat) : 1 ≤ point j := by
    dsimp [point]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hsp.le)
  have hpmono (j : Nat) : point j ≤ point (j+1) := by
    dsimp [point]
    apply add_le_add (le_refl _)
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hsp.le
  have hint (j : Nat) : IntervalIntegrable (fun t => Real.log t*f t) volume (point j) (point (j+1)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (hpmono j)).mpr
    apply hi.mono_set
    intro t ht
    exact lt_of_lt_of_le (by linarith [hp1 j] : (0 : ℝ) < point j) ht.1
  let n := steps*(cutoff-1)
  let bounds := fun j : Nat => EllipticCurve.derivativeCellBounds cs al ah
    (1+(j : Rat)/steps) (1+((j+1 : Nat) : Rat)/steps) bits
  let value := fun j => ∫ t in point j..point (j+1), Real.log t*f t
  unfold EllipticCurve.derivativeFiniteBounds at he
  simp only [Option.bind_eq_bind, Option.pure_def] at he
  change ((List.range n).mapM bounds).bind (fun cells => some (sumIntervalBounds bits cells)) = some out at he
  cases hcells : (List.range n).mapM bounds with
  | none => simp only [hcells, Option.bind_none, reduceCtorEq] at he
  | some cells =>
    have he' : sumIntervalBounds bits cells = out := by simpa only [hcells, Option.bind_some, Option.some.injEq] using he
    rw [← he']
    have h := mapM_sumIntervalBounds_sound (List.range n) bounds value bits cells hcells (by
      intro j _ cell hcell
      have hl : (1 : Rat) ≤ 1+(j : Rat)/steps := by
        exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))
      have hlr : (1+(j : Rat)/steps) ≤ 1+((j+1 : Nat) : Rat)/steps := by
        have hs' : (0 : Rat) < (steps : Rat) := by exact_mod_cast hs
        apply add_le_add (le_refl _)
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hs'.le
      have hh := derivativeCellBounds_sound a cs al ah _ _ bits cell alpha f hl hlr ha ha0 hc hb hf
        (by simpa [point] using hint j) hcell
      simpa [value, point] using hh)
    have hsum : ((List.range n).map value).sum = ∫ t in (1 : ℝ)..(cutoff : ℝ), Real.log t*f t := by
      have hl : ((List.range n).map value).sum = ∑ j ∈ Finset.range n, value j := by
        induction n with
        | zero => simp
        | succ n ih => simp [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      rw [hl]
      have ht := intervalIntegral.sum_integral_adjacent_intervals (n := n) (a := point) (fun j _ => hint j)
      have hp0 : point 0 = 1 := by simp [point]
      have hpn : point n = (cutoff : ℝ) := by
        dsimp [point,n]
        rw [Nat.cast_mul, mul_div_cancel_left₀ _ (ne_of_gt hsp)]
        have hc' : (cutoff-1 : Nat)+1 = cutoff := Nat.sub_add_cancel hcut
        have hc'' : 1+(cutoff-1 : Nat) = cutoff := by omega
        exact_mod_cast hc''
      simpa [value,hp0,hpn] using ht
    rw [hsum] at h
    exact h

end VerifiedLcalc.Numerics
