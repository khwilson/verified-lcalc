module

public import VerifiedLcalc.EllipticCurve.Correctness
public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic
public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

namespace VerifiedLcalc.Modularity

open EllipticCurve

/-- Coprimality of discriminant and c4 is the integral semistable-model
criterion used by the temporary compatibility assumption. -/
def SemistableModel (equation : (WeierstrassCurve ℤ)) : Prop :=
  Int.gcd (equation.Δ) equation.c₄ = 1
  deriving Decidable

noncomputable def semistableLevel (equation : (WeierstrassCurve ℤ)) : Nat :=
  ∏ p ∈ (equation.Δ).natAbs.primeFactors, p

noncomputable def semistableSign (equation : (WeierstrassCurve ℤ)) : Int :=
  -(∏ p ∈ (equation.Δ).natAbs.primeFactors,
    if hp : p.Prime then
      letI : Fact p.Prime := ⟨hp⟩;
      -((equation.baseChange (ZMod p)).frobeniusTrace)
    else 1)

/-- A modular realization using mathlib's actual curve Euler coefficients, cusp
forms and q-expansions. The level and Fricke sign are existential, not arbitrary
supplied inputs. This package does not assume a numerical evaluation formula. -/
structure ModularRealization (equation : (WeierstrassCurve ℤ)) where
  level : Nat
  positiveLevel : 0 < level
  rootNumber : Int
  rootNumberSign : rootNumber = 1 ∨ rootNumber = -1
  form : CuspForm (CongruenceSubgroup.Gamma0 level : Subgroup (GL (Fin 2) ℝ)) 2
  coefficients : ∀ n : Nat, (UpperHalfPlane.qExpansion 1 form).coeff n =
    ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ)
  frickeImaginaryAxis : ∀ t : ℝ, 0 < t →
    form (UpperHalfPlane.ofComplex (Complex.I * ((1 / t) / Real.sqrt level))) =
      (rootNumber : ℂ) * (t : ℂ) ^ 2 *
        form (UpperHalfPlane.ofComplex (Complex.I * (t / Real.sqrt level)))
  goodPrimeCoefficients : ∀ (p : Nat) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    (equation.baseChange (ZMod p)).Δ ≠ 0 →
      (UpperHalfPlane.qExpansion 1 form).coeff p =
        ((equation.baseChange (ZMod p)).frobeniusTrace : ℂ)
  /-- General semistable arithmetic-conductor compatibility, user-authorized
  as an extension of the temporary axiom on 2026-11-17. -/
  semistableLevel_eq : SemistableModel equation → level = semistableLevel equation
  /-- The real-place sign times the multiplicative local signs. This does not
  assume an arbitrary caller-provided sign. -/
  semistableSign_eq : SemistableModel equation → rootNumber = semistableSign equation

/-- Normalization follows from matching every actual curve coefficient; it is
not a separate field of the modularity assumption. -/
theorem ModularRealization.normalized {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) : (UpperHalfPlane.qExpansion 1 m.form).coeff 1 = 1 := by
  rw [m.coefficients, WeierstrassCurve.LFunction_apply_one]
  norm_num

/-- Numerical compatibility is derived from the canonical mathematical trace,
not supplied as an assumption about a particular evaluation algorithm. -/
theorem ModularRealization.goodPrimeCoefficients_computed {e : WeierstrassCurve ℤ}
    (m : ModularRealization e) (p : ℕ) (hp : p.Prime)
    (hg : goodReduction e p = true) :
    (UpperHalfPlane.qExpansion 1 m.form).coeff p = (computeFrobeniusTrace e p : ℂ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := m.goodPrimeCoefficients p hp ((goodReduction_correct e p).mp hg)
  simpa only [← computeFrobeniusTrace_correct e p] using h

/-- Mathlib's entire L-function of a supplied cusp-form witness. Its
coefficients match the actual curve. -/
noncomputable def ModularRealization.formL {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) : ℂ → ℂ :=
  letI : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  ModularForm.L (by decide : (0 : ℤ) < 2) m.form

/-- Entirety for any supplied realization is already a mathlib theorem; no
modularity axiom is needed to prove this general implication. -/
theorem ModularRealization.formL_differentiable {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) : Differentiable ℂ m.formL := by
  letI : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  exact CuspForm.differentiable_L (by decide : (0 : ℤ) < 2) m.form


/-- The supplied realization identifies the continued function with the actual
curve coefficient series on a convergence half-plane. No custom axiom occurs
in this implication: it works for any proved modular realization. -/
theorem ModularRealization.formL_hasSum {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) (s : ℂ) (hs : 2 < s.re) :
    HasSum (fun n : Nat => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ) / (n : ℂ) ^ s)
      (m.formL s) := by
  letI : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  have h := CuspForm.hasSum_L (by decide : (0 : ℤ) < 2) m.form
    (by norm_num; exact hs)
  simpa [m.coefficients, ModularRealization.formL] using h

/-- Agreement with mathlib's named curve L-series where that series converges.
This equality is not asserted for the raw L-series definition at the center. -/
theorem ModularRealization.formL_eq_curveLSeries {equation : (WeierstrassCurve ℤ)}
    (m : ModularRealization equation) (s : ℂ) (hs : 2 < s.re) :
    (WeierstrassCurve.baseChange equation ℚ).LSeries s = m.formL s := by
  change LSeries (fun n => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ)) s = m.formL s
  have hs0 : s ≠ 0 := by
    intro hz
    norm_num [hz] at hs
  have h := m.formL_hasSum s hs
  rw [← funext (LSeries.term_of_ne_zero' hs0
    (fun n => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ)))] at h
  exact LSeriesHasSum.LSeries_eq h

end VerifiedLcalc.Modularity
