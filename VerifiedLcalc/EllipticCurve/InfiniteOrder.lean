module

public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Discriminant
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral
public import VerifiedLcalc.EllipticCurve.AlgebraicRank

/-!
# Exact infinite-order certificates for integral points

For a long integral Weierstrass equation, put `κ = 2y + a₁x + a₃`.
TauCeti's discriminant companion to Nagell–Lutz proves that torsion forces
`κ = 0 ∨ κ² ∣ 4Δ`. Its contrapositive is a finite integer check. Failure is
inconclusive: this sufficient test does not classify all torsion points.
-/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- A sufficient exact test for infinite order, without point search. -/
def infiniteOrderCheck (W : WeierstrassCurve ℤ) (x y : Int) : Bool :=
  let κ := 2 * y + W.a₁ * x + W.a₃
  decide (κ ≠ 0 ∧ ¬ κ ^ 2 ∣ 4 * W.Δ)

/-- Soundness against Mathlib's finite-additive-order predicate, for the
actual rational point constructed from the supplied integral solution. -/
theorem infiniteOrderCheck_sound (W : WeierstrassCurve ℤ)
    [(W.baseChange ℚ).IsElliptic] (x y : Int) (h : W.toAffine.Equation x y)
    (hc : infiniteOrderCheck W x y = true) :
    ¬ IsOfFinAddOrder (W.pointOfIntegralSolution x y h) := by
  intro ht
  rw [W.pointOfIntegralSolution_eq_some] at ht
  have hd := WeierstrassCurve.evalEval_ψ₂_eq_zero_or_sq_dvd_four_mul_Δ_rat _ ht
    (x₀ := x) (y₀ := y) rfl rfl
  have checks : (2 * y + W.a₁ * x + W.a₃) ≠ 0 ∧
      ¬ (2 * y + W.a₁ * x + W.a₃) ^ 2 ∣ 4 * W.Δ := of_decide_eq_true hc
  have he : W.ψ₂.evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by
    exact W.toAffine.evalEval_polynomialY x y
  rw [he] at hd
  exact hd.elim checks.1 checks.2

end VerifiedLcalc.EllipticCurve
