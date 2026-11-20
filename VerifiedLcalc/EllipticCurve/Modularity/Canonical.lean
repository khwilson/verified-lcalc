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

end VerifiedLcalc.Modularity
