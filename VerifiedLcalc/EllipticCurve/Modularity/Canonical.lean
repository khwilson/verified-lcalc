module

public import VerifiedLcalc.Assumptions.Modularity

@[expose] public section
namespace VerifiedLcalc.Modularity

/-- The single assumed package, before forgetting its arithmetic fields. -/
noncomputable def arithmeticModularWitness (equation : (WeierstrassCurve ℤ))
    (nonsingular : equation.Δ ≠ 0) : ArithmeticModularRealization equation :=
  Classical.choice (Assumptions.ellipticModularity equation nonsingular)

/-- Choice of a normalized weight-two cusp form from the authorized package. -/
noncomputable def modularWitness (equation : (WeierstrassCurve ℤ))
    (nonsingular : equation.Δ ≠ 0) : ModularRealization equation :=
  (arithmeticModularWitness equation nonsingular).toModularRealization

theorem modularWitness_normalized (equation : (WeierstrassCurve ℤ))
    (nonsingular : equation.Δ ≠ 0) :
    (UpperHalfPlane.qExpansion 1 (modularWitness equation nonsingular).form).coeff 1 = 1 :=
  (modularWitness equation nonsingular).normalized

theorem modularWitness_goodPrime (equation : (WeierstrassCurve ℤ))
    (nonsingular : equation.Δ ≠ 0) (p : Nat)
    (prime : p.Prime) (good : EllipticCurve.goodReduction equation p = true) :
    (UpperHalfPlane.qExpansion 1 (modularWitness equation nonsingular).form).coeff p =
      (EllipticCurve.frobeniusTrace equation p : ℂ) :=
  (modularWitness equation nonsingular).goodPrimeCoefficients p prime good

/-- This theorem's axiom audit includes `ellipticModularity`. -/
theorem modularWitness_formL_differentiable (equation : (WeierstrassCurve ℤ))
    (nonsingular : equation.Δ ≠ 0) :
    Differentiable ℂ (modularWitness equation nonsingular).formL :=
  (modularWitness equation nonsingular).formL_differentiable


theorem modularWitness_formL_hasSum (equation : (WeierstrassCurve ℤ))
    (nonsingular : equation.Δ ≠ 0) (s : ℂ) (hs : 2 < s.re) :
    HasSum (fun n : Nat => ((WeierstrassCurve.baseChange equation ℚ).LFunction n : ℂ) /
      (n : ℂ) ^ s) ((modularWitness equation nonsingular).formL s) :=
  (modularWitness equation nonsingular).formL_hasSum s hs

end VerifiedLcalc.Modularity
