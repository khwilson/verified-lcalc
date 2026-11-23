module

public import VerifiedLcalc.EllipticCurve.Modularity.FirstDerivative
public import VerifiedLcalc.EllipticCurve.Derivative
public import VerifiedLcalc.EllipticCurve.GlobalBounds

/-! # Soundness of first-derivative enclosures for a modular realization -/

@[expose] public section
namespace VerifiedLcalc.Modularity
open EllipticCurve Numerics Set MeasureTheory

/-- All numerical evidence is discharged for the actual realizing cusp form. -/
theorem ModularRealization.derivativePayload_contains {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (r : DerivativeResult) (hr : DerivativePayloadCorrect r)
    (hN : r.conductor = m.level)
    (hc : r.coefficients = (List.range r.termLimit).map (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j+1))) :
    r.box.Contains (Complex.ofReal (∫ t : ℝ in Ioi 1, Real.log t*(m.imaginaryFunction t).re)) := by
  have hbc (j : Nat) : |((WeierstrassCurve.baseChange e ℚ).LFunction (j+1) : ℝ)| ≤ ((j+1 : Nat) : ℝ)^3 := by
    exact_mod_cast LFunction_abs_le_cube (WeierstrassCurve.baseChange e ℚ) (j+1)
  have hf (t : ℝ) (ht : 0 < t) : HasSum
      (fun j => ((WeierstrassCurve.baseChange e ℚ).LFunction (j+1) : ℝ)*
        Real.exp (-(2*Real.pi/Real.sqrt r.conductor)*t)^(j+1)) (m.imaginaryFunction t).re := by
    convert m.imaginaryFunction_re_hasSum t ht using 1
    funext j
    rw [← Real.exp_natCast_mul, hN]
    congr 1
    push_cast
    ring
  have hi : IntegrableOn (fun t => Real.log t • m.imaginaryFunction t) (Ioi 0) := by
    simpa [MellinConvergent] using m.mellin_first_derivative.1
  have hir : IntegrableOn (fun t => Real.log t*(m.imaginaryFunction t).re) (Ioi 0) := by
    simpa only [RCLike.smul_re, RCLike.re_to_complex] using hi.re
  exact EllipticCurve.derivativePayload_contains r hr _ _ hc hbc hf hir

/-- The exported scalar interval encloses the actual real part of L'(1). -/
theorem ModularRealization.realDerivativeBounds_contains {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (r : DerivativeResult) (hr : DerivativePayloadCorrect r)
    (hN : r.conductor = m.level) (hw : m.rootNumber = -1)
    (hc : r.coefficients = (List.range r.termLimit).map (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j+1))) :
    r.realDerivativeBounds.Contains (deriv m.formL 1).re := by
  have ha := alphaBounds_correct r.conductor r.policy.precisionBits hr.1
  rw [← hr.2.2.2.2.1, ← hr.2.2.2.2.2.1] at ha
  have hscale : RealInterval.Contains (2*r.alphaLo,2*r.alphaHi)
      (4*Real.pi/Real.sqrt m.level) := by
    change (((2*r.alphaLo : Rat) : ℝ) ≤ _ ∧ _ ≤ ((2*r.alphaHi : Rat) : ℝ))
    push_cast
    rw [← hN]
    rw [show (4*Real.pi/Real.sqrt r.conductor : ℝ) = 2*(2*Real.pi/Real.sqrt r.conductor) by ring]
    constructor <;> nlinarith [ha.1,ha.2]
  have hJ := m.derivativePayload_contains r hr hN hc
  have hJ' : RealInterval.Contains (r.box.reLo,r.box.reHi)
      (∫ t : ℝ in Ioi 1, Real.log t*(m.imaginaryFunction t).re) := by
    simpa [Numerics.RealInterval.Contains] using hJ.1
  rw [m.deriv_one_re_integral hw]
  exact Numerics.intervalMul_sound _ _ _ _ hscale hJ'

/-- Exact rank one needs both an exact central zero and a proved nonzero
first derivative. A small central value is never used as a zero certificate. -/
theorem ModularRealization.analyticOrder_one_of_derivativePayload {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (r : DerivativeResult) (hr : DerivativePayloadCorrect r)
    (hN : r.conductor = m.level) (hw : m.rootNumber = -1)
    (hc : r.coefficients = (List.range r.termLimit).map (fun j => (WeierstrassCurve.baseChange e ℚ).LFunction (j+1)))
    (hz : r.box.excludesZero = true) : analyticOrderAt m.formL (1 : ℂ) = 1 := by
  apply (m.formL_differentiable.analyticAt 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (m.central_zero_of_negative_sign hw)
  intro hd
  have he := congrArg Complex.re hd
  rw [m.deriv_one_re_integral hw, Complex.zero_re] at he
  have hscale : (4*Real.pi/Real.sqrt m.level : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact div_pos (mul_pos (by norm_num) Real.pi_pos)
      (Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel))
  have hJ := (mul_eq_zero.mp he).resolve_left hscale
  have hbox := m.derivativePayload_contains r hr hN hc
  have hn := Box.excludesZero_sound hz hbox
  apply hn
  rw [hJ]
  rfl
end VerifiedLcalc.Modularity
