/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Ordinary p-adic sigma normalization

The local specification uses the formal parameter `t = -x/y` and the invariant differential
on the given Weierstrass equation. The differential characterization is described by
Blakestad–Grant, *On the universal p-adic sigma and zeta functions*, Theorem 8 and Remark 11
(https://arxiv.org/abs/1903.02480). The formal inverse in a general Weierstrass equation replaces
substitution of `-t` on a short model.
-/

@[expose] public section

open scoped LaurentSeries

namespace VerifiedLcalc.EllipticCurve

/-- The formal expansion of `s = -1/y` at the point at infinity, in the parameter
`t = -x/y`. The equation follows by substituting `x = t/s` and `y = -1/s`. -/
def IsWeierstrassParameterSeries {K : Type*} [Field K] (E : WeierstrassCurve K)
    (s : PowerSeries K) : Prop :=
  let t : PowerSeries K := PowerSeries.X
  let c := PowerSeries.C (R := K)
  PowerSeries.constantCoeff s = 0 ∧
    s = t ^ 3 + c E.a₁ * t * s + c E.a₂ * t ^ 2 * s + c E.a₃ * s ^ 2 +
      c E.a₄ * t * s ^ 2 + c E.a₆ * s ^ 3

/-- The invariant derivation dual to `dx / (2y + a₁x + a₃)`, on Laurent series in `t`. -/
noncomputable def weierstrassParameterDeriv {K : Type*} [Field K]
    (E : WeierstrassCurve K) (s : PowerSeries K) (f : K⸨X⸩) : K⸨X⸩ :=
  let x : K⸨X⸩ := (PowerSeries.X : PowerSeries K) / (s : K⸨X⸩)
  let y : K⸨X⸩ := -1 / (s : K⸨X⸩)
  let c (a : K) : K⸨X⸩ := ((PowerSeries.C a : PowerSeries K) : K⸨X⸩)
  ((2 * y + c E.a₁ * x + c E.a₃) / LaurentSeries.derivative K x) *
    LaurentSeries.derivative K f

/-- The change to the parameter under negation of a point. The denominator of this
power series has constant coefficient one when `s` is the expansion at infinity. -/
noncomputable def weierstrassParameterNeg {K : Type*} [Field K] (E : WeierstrassCurve K)
    (s : PowerSeries K) : PowerSeries K :=
  let t : PowerSeries K := PowerSeries.X
  (-t) * (1 - PowerSeries.C E.a₁ * t - PowerSeries.C E.a₃ * s)⁻¹

/-- The normalized integral sigma function is odd under formal negation, has leading
term `t`, and satisfies the invariant differential equation with a constant right side.
Every coefficient is integral in the p-adic norm. -/
def IsNormalizedOrdinarySigma {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve ℚ_[p])
    (s sigma : PowerSeries ℚ_[p]) : Prop :=
  let D := weierstrassParameterDeriv E s
  let x : ℚ_[p]⸨X⸩ := (PowerSeries.X : PowerSeries ℚ_[p]) / (s : ℚ_[p]⸨X⸩)
  PowerSeries.constantCoeff sigma = 0 ∧
    PowerSeries.coeff 1 sigma = 1 ∧
    (∀ n, ‖PowerSeries.coeff n sigma‖ ≤ 1) ∧
    PowerSeries.subst (weierstrassParameterNeg E s) sigma = -sigma ∧
    ∃ beta : ℚ_[p], D (D (sigma : ℚ_[p]⸨X⸩) / (sigma : ℚ_[p]⸨X⸩)) + x =
      ((PowerSeries.C beta : PowerSeries ℚ_[p]) : ℚ_[p]⸨X⸩)

/-- Exact rational logarithm prefix evaluated at a supplied rational argument. -/
def rationalPadicLogPrefix (z : ℚ) (terms : ℕ) : ℚ :=
  ((List.range terms).map fun k => (-1 : ℚ) ^ k * z ^ (k + 1) / ((k + 1 : ℕ) : ℚ)).sum

/-- Evaluate the formal sigma series at a parameter in the open p-adic unit ball.
Integral coefficients and the formal parameter bound imply convergence. -/
noncomputable def evalOrdinarySigma {p : ℕ} [Fact p.Prime]
    (sigma : PowerSeries ℚ_[p]) (t : ℚ_[p]) : ℚ_[p] :=
  ∑' k : ℕ, PowerSeries.coeff k sigma * t ^ k

/-- Terms of the logarithm of `1 + z`, on the open p-adic unit ball. -/
noncomputable def padicLogOneAddTerm {p : ℕ} [Fact p.Prime]
    (z : ℚ_[p]) (k : ℕ) : ℚ_[p] :=
  (-1 : ℚ_[p]) ^ k * z ^ (k + 1) / ((k + 1 : ℕ) : ℚ_[p])

/-- Argument of the cyclotomic logarithm series for the sigma value at the marked point.
Raising a unit to the `(p - 1)`st power removes its root of unity. -/
noncomputable def ordinarySigmaLogArgument {p : ℕ} [Fact p.Prime]
    (sigma : PowerSeries ℚ_[p]) (x y : ℚ) (d : ℕ) : ℚ_[p] :=
  (evalOrdinarySigma sigma (-(x : ℚ_[p]) / (y : ℚ_[p])) / (d : ℚ_[p])) ^ (p - 1) - 1

/-- The rational scale for the ordinary height, including the unit logarithm's
division by `p - 1` and division by the square of the point multiple. -/
def ordinaryPadicHeightScale (p n : ℕ) : ℚ :=
  -2 / (((p - 1 : ℕ) : ℚ) * (n : ℚ) ^ 2)

/-- Ordinary height of the chosen point from the canonical sigma function at the
multiple `nP`. The arguments `x, y` are coordinates of that multiple and `d` is
its positive denominator in the convention `x = a/d²`. -/
noncomputable def ordinaryPadicHeightAtMultiple {p : ℕ} [Fact p.Prime]
    (sigma : PowerSeries ℚ_[p]) (x y : ℚ) (d n : ℕ) : ℚ_[p] :=
  (ordinaryPadicHeightScale p n : ℚ_[p]) *
    ∑' k : ℕ, padicLogOneAddTerm (ordinarySigmaLogArgument sigma x y d) k

/-- The determinant of the height matrix on the single rank-one basis vector.
The arguments describe the chosen multiple of its actual lift. -/
noncomputable def ordinaryRankOnePadicRegulator {p : ℕ} [Fact p.Prime]
    (sigma : PowerSeries ℚ_[p]) (x y : ℚ) (d n : ℕ) : ℚ_[p] :=
  Matrix.det (Matrix.of fun (_ : Fin 1) (_ : Fin 1) =>
    ordinaryPadicHeightAtMultiple sigma x y d n)

/-- The rank-one determinant is the normalized height of the basis lift. -/
theorem ordinaryRankOnePadicRegulator_eq_height {p : ℕ} [Fact p.Prime]
    (sigma : PowerSeries ℚ_[p]) (x y : ℚ) (d n : ℕ) :
    ordinaryRankOnePadicRegulator sigma x y d n =
      ordinaryPadicHeightAtMultiple sigma x y d n := by
  rw [ordinaryRankOnePadicRegulator, Matrix.det_fin_one, Matrix.of_apply]

end VerifiedLcalc.EllipticCurve
