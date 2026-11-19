module

public import VerifiedLcalc.Assumptions.FullModularityStatement

@[expose] public section

namespace VerifiedLcalc.Assumptions

/-- TEMPORARY USER-AUTHORIZED AXIOM. This is elliptic modularity with coefficient and Fricke matching, not FLT,
BSD, an exact-vanishing principle, or a numerical correctness assumption.
Replace with a proof of the same proposition when a compatible formalization
has been imported and audited. Deliberately absent from the default imports. -/
axiom ellipticModularity : GeneralEllipticModularity

/-- The single assumed package, before forgetting its arithmetic fields. -/
noncomputable def arithmeticModularWitness (equation : Artifacts.CurveEquation)
    (nonsingular : EllipticCurve.discriminant equation ≠ 0) : ArithmeticModularRealization equation :=
  Classical.choice (ellipticModularity equation nonsingular)

/-- Choice of a normalized weight-two cusp form from the authorized package. -/
noncomputable def modularWitness (equation : Artifacts.CurveEquation)
    (nonsingular : EllipticCurve.discriminant equation ≠ 0) : ModularRealization equation :=
  (arithmeticModularWitness equation nonsingular).toModularRealization

theorem modularWitness_normalized (equation : Artifacts.CurveEquation)
    (nonsingular : EllipticCurve.discriminant equation ≠ 0) :
    (UpperHalfPlane.qExpansion 1 (modularWitness equation nonsingular).form).coeff 1 = 1 :=
  (modularWitness equation nonsingular).normalized

theorem modularWitness_goodPrime (equation : Artifacts.CurveEquation)
    (nonsingular : EllipticCurve.discriminant equation ≠ 0) (p : Nat)
    (prime : p.Prime) (good : EllipticCurve.goodReduction equation p = true) :
    (UpperHalfPlane.qExpansion 1 (modularWitness equation nonsingular).form).coeff p =
      (EllipticCurve.frobeniusTrace equation p : ℂ) :=
  (modularWitness equation nonsingular).goodPrimeCoefficients p prime good

/-- This theorem's axiom audit includes `ellipticModularity`. -/
theorem modularWitness_formL_differentiable (equation : Artifacts.CurveEquation)
    (nonsingular : EllipticCurve.discriminant equation ≠ 0) :
    Differentiable ℂ (modularWitness equation nonsingular).formL :=
  (modularWitness equation nonsingular).formL_differentiable


theorem modularWitness_formL_hasSum (equation : Artifacts.CurveEquation)
    (nonsingular : EllipticCurve.discriminant equation ≠ 0) (s : ℂ) (hs : 2 < s.re) :
    HasSum (fun n : Nat => ((EllipticCurve.weierstrass equation ℚ).LFunction n : ℂ) /
      (n : ℂ) ^ s) ((modularWitness equation nonsingular).formL s) :=
  (modularWitness equation nonsingular).formL_hasSum s hs

end VerifiedLcalc.Assumptions
