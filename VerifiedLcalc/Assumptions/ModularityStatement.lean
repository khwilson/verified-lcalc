module

public import VerifiedLcalc.EllipticCurve.Correctness
public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

namespace VerifiedLcalc.Assumptions

open EllipticCurve

/-- The usual Gamma_0 level as a subgroup of GL_2(R). -/
def gamma0 (level : Nat) : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 level).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- Coprimality of discriminant and c4 is the integral semistable-model
criterion used by the temporary compatibility assumption. -/
def SemistableModel (equation : Artifacts.CurveEquation) : Prop :=
  Int.gcd (discriminant equation) (weierstrass equation Int).c₄ = 1
  deriving Decidable

noncomputable def semistableLevel (equation : Artifacts.CurveEquation) : Nat :=
  ∏ p ∈ (discriminant equation).natAbs.primeFactors, p

noncomputable def semistableSign (equation : Artifacts.CurveEquation) : Int :=
  -(∏ p ∈ (discriminant equation).natAbs.primeFactors, -(frobeniusTrace equation p))

/-- A modular realization using mathlib's actual curve Euler coefficients, cusp
forms and q-expansions. The level and Fricke sign are existential, not arbitrary
supplied inputs. This package does not assume a numerical evaluation formula. -/
structure ModularRealization (equation : Artifacts.CurveEquation) where
  level : Nat
  positiveLevel : 0 < level
  arithmetic : (gamma0 level).IsArithmetic
  widthOne : (gamma0 level).strictWidthInfty = 1
  rootNumber : Int
  rootNumberSign : rootNumber = 1 ∨ rootNumber = -1
  form : CuspForm (gamma0 level) 2
  normalized : (UpperHalfPlane.qExpansion 1 form).coeff 1 = 1
  coefficients : ∀ n : Nat, (UpperHalfPlane.qExpansion 1 form).coeff n =
    ((weierstrass equation ℚ).LFunction n : ℂ)
  frickeImaginaryAxis : ∀ t : ℝ, 0 < t →
    form (UpperHalfPlane.ofComplex (Complex.I * ((1 / t) / Real.sqrt level))) =
      (rootNumber : ℂ) * (t : ℂ) ^ 2 *
        form (UpperHalfPlane.ofComplex (Complex.I * (t / Real.sqrt level)))
  goodPrimeCoefficients : ∀ p : Nat, p.Prime → goodReduction equation p = true →
    (UpperHalfPlane.qExpansion 1 form).coeff p = (frobeniusTrace equation p : ℂ)
  /-- General semistable arithmetic-conductor compatibility, user-authorized
  as an extension of the temporary axiom on 2026-11-17. -/
  semistableLevel_eq : SemistableModel equation → level = semistableLevel equation
  /-- The real-place sign times the multiplicative local signs. This does not
  assume an arbitrary caller-provided sign. -/
  semistableSign_eq : SemistableModel equation → rootNumber = semistableSign equation

/-- The exact proposition assumed in the opt-in axiom module. This module
itself adds no axioms. Modularity is assumed only for nonsingular equations. -/
def EllipticModularity : Prop :=
  ∀ equation : Artifacts.CurveEquation, discriminant equation ≠ 0 →
    Nonempty (ModularRealization equation)

/-- Mathlib's entire L-function of a supplied cusp-form witness. Its
coefficients match the actual curve. -/
noncomputable def ModularRealization.formL {equation : Artifacts.CurveEquation}
    (m : ModularRealization equation) : ℂ → ℂ :=
  letI := m.arithmetic
  ModularForm.L (by decide : (0 : ℤ) < 2) m.form

/-- Entirety for any supplied realization is already a mathlib theorem; no
modularity axiom is needed to prove this general implication. -/
theorem ModularRealization.formL_differentiable {equation : Artifacts.CurveEquation}
    (m : ModularRealization equation) : Differentiable ℂ m.formL := by
  let _ := m.arithmetic
  exact CuspForm.differentiable_L (by decide : (0 : ℤ) < 2) m.form


/-- The supplied realization identifies the continued function with the actual
curve coefficient series on a convergence half-plane. No custom axiom occurs
in this implication: it works for any proved modular realization. -/
theorem ModularRealization.formL_hasSum {equation : Artifacts.CurveEquation}
    (m : ModularRealization equation) (s : ℂ) (hs : 2 < s.re) :
    HasSum (fun n : Nat => ((weierstrass equation ℚ).LFunction n : ℂ) / (n : ℂ) ^ s)
      (m.formL s) := by
  let _ := m.arithmetic
  have h := CuspForm.hasSum_L (by decide : (0 : ℤ) < 2) m.form
    (by norm_num; exact hs)
  simpa [m.widthOne, m.coefficients, ModularRealization.formL] using h

/-- Agreement with mathlib's named curve L-series where that series converges.
This equality is not asserted for the raw L-series definition at the center. -/
theorem ModularRealization.formL_eq_curveLSeries {equation : Artifacts.CurveEquation}
    (m : ModularRealization equation) (s : ℂ) (hs : 2 < s.re) :
    (weierstrass equation ℚ).LSeries s = m.formL s := by
  change LSeries (fun n => ((weierstrass equation ℚ).LFunction n : ℂ)) s = m.formL s
  have hs0 : s ≠ 0 := by
    intro hz
    norm_num [hz] at hs
  have h := m.formL_hasSum s hs
  rw [← funext (LSeries.term_of_ne_zero' hs0
    (fun n => ((weierstrass equation ℚ).LFunction n : ℂ)))] at h
  exact LSeriesHasSum.LSeries_eq h

end VerifiedLcalc.Assumptions
