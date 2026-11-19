module

public import VerifiedLcalc.Assumptions.ModularityStatement
public import VerifiedLcalc.EllipticCurve.WildArithmetic

@[expose] public section
namespace VerifiedLcalc.Assumptions
open EllipticCurve

/-- General modularity with standard arithmetic compatibility. The local arithmetic
identifications below are part of the authorized temporary assumption, not
proved conductor/root-number theory. Their right sides are mathematical local
formulas, independent of caller inputs and external reference data.
Wild additive reduction is identified only from validated Tate transcripts
and the explicit Halberstadt mathematical tables. -/
structure ArithmeticModularRealization (e : Artifacts.CurveEquation)
    extends ModularRealization e where
  tameLevel_eq : GloballyMinimalInput e → tameAtWild e = true → level = tameLevel e
  tameSign_eq : GloballyMinimalInput e → tameAtWild e = true → rootNumber = tameSign e
  /-- Standard Tate/Ogg arithmetic-conductor compatibility. -/
  wildLevel_eq : GloballyMinimalInput e → ∀ d : WildData, d.Valid e → level = wildLevel e d
  /-- Standard Halberstadt local-epsilon-factor compatibility. -/
  wildSign_eq : GloballyMinimalInput e → ∀ d : WildData, d.Valid e → rootNumber = wildSign e d

/-- The strengthened, explicitly arithmetic general-modularity package. -/
def GeneralEllipticModularity : Prop :=
  ∀ e : Artifacts.CurveEquation, discriminant e ≠ 0 →
    Nonempty (ArithmeticModularRealization e)

end VerifiedLcalc.Assumptions
