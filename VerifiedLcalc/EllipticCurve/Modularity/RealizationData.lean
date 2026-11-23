/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! # A weight-two modular realization of a rational elliptic curve -/

@[expose] public section

namespace VerifiedLcalc.Modularity

/-- Coprimality of discriminant and c4 is the integral semistable-model
criterion used by the temporary compatibility assumption. -/
def SemistableModel (equation : WeierstrassCurve ℤ) : Prop :=
  Int.gcd (equation.Δ) equation.c₄ = 1
  deriving Decidable

/-- The product of the primes in the discriminant of a semistable model. -/
noncomputable def semistableLevel (equation : WeierstrassCurve ℤ) : Nat :=
  ∏ p ∈ (equation.Δ).natAbs.primeFactors, p

/-- The product of the local signs at the bad primes and the real-place sign. -/
noncomputable def semistableSign (equation : WeierstrassCurve ℤ) : Int :=
  -(∏ p ∈ (equation.Δ).natAbs.primeFactors,
    if hp : p.Prime then
      letI : Fact p.Prime := ⟨hp⟩;
      -((equation.baseChange (ZMod p)).frobeniusTrace)
    else 1)

/-- A modular realization using mathlib's actual curve Euler coefficients, cusp
forms and q-expansions. The level and Fricke sign are existential, not arbitrary
supplied inputs. This package does not assume a numerical evaluation formula. -/
structure ModularRealization (equation : WeierstrassCurve ℤ) where
  /-- Level of the supplied cusp form. -/
  level : Nat
  /-- Positivity of the level used in the Mellin normalization. -/
  positiveLevel : 0 < level
  /-- Root number of the supplied modular realization. -/
  rootNumber : Int
  /-- The root number is a sign. -/
  rootNumberSign : rootNumber = 1 ∨ rootNumber = -1
  /-- Supplied weight-two cusp form at the stated level. -/
  form : CuspForm (CongruenceSubgroup.Gamma0 level : Subgroup (GL (Fin 2) ℝ)) 2
  /-- Fourier coefficients agree with the arithmetic curve coefficients. -/
  coefficients : ∀ n : Nat, (UpperHalfPlane.qExpansion 1 form).coeff n =
    ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ)
  /-- Fricke identity on the positive imaginary axis. -/
  frickeImaginaryAxis : ∀ t : ℝ, 0 < t →
    form (UpperHalfPlane.ofComplex (Complex.I * ((1 / t) / Real.sqrt level))) =
      (rootNumber : ℂ) * (t : ℂ) ^ 2 *
        form (UpperHalfPlane.ofComplex (Complex.I * (t / Real.sqrt level)))
  /-- Prime coefficients agree with the good-reduction Frobenius traces. -/
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

/-- Mathlib's entire L-function of a supplied cusp-form witness. Its
coefficients match the actual curve. -/
noncomputable def ModularRealization.formL {equation : WeierstrassCurve ℤ}
    (m : ModularRealization equation) : ℂ → ℂ :=
  letI : NeZero m.level := ⟨Nat.ne_of_gt m.positiveLevel⟩
  ModularForm.L (by decide : (0 : ℤ) < 2) m.form

end VerifiedLcalc.Modularity
