module

public import VerifiedLcalc.EllipticCurve.Modularity.ArithmeticRealization

@[expose] public section
namespace VerifiedLcalc.Assumptions

/-- General modularity for every nonsingular integral equation. The realization
includes coefficient/Fricke matching and semistable, tame and wild arithmetic
conductor/root-number compatibility; see `ArithmeticModularRealization`. -/
def GeneralEllipticModularity : Prop :=
  ∀ e : WeierstrassCurve ℤ, e.Δ ≠ 0 →
    Nonempty (Modularity.ArithmeticModularRealization e)

/-- TEMPORARY USER-AUTHORIZED AXIOM: general elliptic modularity, including
arithmetic conductor/sign compatibility. This does not assume numerical
correctness, BSD or exact vanishing. The default library does not import it. -/
axiom ellipticModularity : GeneralEllipticModularity

end VerifiedLcalc.Assumptions
