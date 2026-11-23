module

public import VerifiedLcalc.Verification.NegativeSign
public import VerifiedLcalc.EllipticCurve.ReductionArithmetic

/-! # Central vanishing and a rank bound from a negative tame root number -/

@[expose] public section
namespace VerifiedLcalc.Certification
open Modularity EllipticCurve
open EllipticCurve

/-- Exact central vanishing from the tame sign formula. No conductor hint or
numerical near-zero test enters this implication. -/
theorem central_zero_of_tame_negative (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (v : MinimalityWitness) (hv : v.Valid e)
    (ht : tameAtWild e = true) (hw : tameSignFast e = -1) :
    (modularWitness e hn).formL 1 = 0 := by
  let : (e.baseChange ℚ).IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (e.Δ : ℚ) ≠ 0 by exact_mod_cast hn)⟩
  apply (modularWitness e hn).central_zero_of_negative_sign
  exact ((arithmeticModularWitness e hn).tameSign_eq (globalMinimal_of_witness e v hv) ht).trans
    ((tameSign_eq_fast e ht).trans hw)

/-- A verified negative tame root number gives analytic order at least one at the center. -/
theorem rank_lower_bound_of_tame_negative (e : (WeierstrassCurve ℤ))
    (hn : e.Δ ≠ 0) (v : MinimalityWitness) (hv : v.Valid e)
    (ht : tameAtWild e = true) (hw : tameSignFast e = -1) :
    1 ≤ analyticOrderAt (modularWitness e hn).formL (1 : ℂ) := by
  have hz := central_zero_of_tame_negative e hn v hv ht hw
  have hne : analyticOrderAt (modularWitness e hn).formL (1 : ℂ) ≠ 0 :=
    ((modularWitness e hn).formL_differentiable.analyticAt 1).analyticOrderAt_ne_zero.mpr hz
  exact Order.one_le_iff_ne_zero.mpr hne
end VerifiedLcalc.Certification
