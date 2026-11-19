module

public import VerifiedLcalc.EllipticCurve.Modularity.Realization
public import VerifiedLcalc.EllipticCurve.Tate.WildArithmetic

@[expose] public section
namespace VerifiedLcalc.Modularity
open EllipticCurve

/-- General modularity with standard arithmetic compatibility. The local arithmetic
identifications below are part of the authorized temporary assumption, not
proved conductor/root-number theory. Their right sides are mathematical local
formulas, independent of caller inputs and external reference data.
Wild additive reduction is identified only from validated Tate transcripts
and the explicit Halberstadt mathematical tables. -/
structure ArithmeticModularRealization (e : (WeierstrassCurve ℤ))
    extends ModularRealization e where
  tameLevel_eq : GloballyMinimalInput e → tameAtWild e = true → level = tameLevel e
  tameSign_eq : GloballyMinimalInput e → tameAtWild e = true → rootNumber = tameSign e
  /-- Standard Tate/Ogg arithmetic-conductor compatibility. -/
  wildLevel_eq : GloballyMinimalInput e → ∀ d : WildData, d.Valid e → level = wildLevel e d
  /-- Standard Halberstadt local-epsilon-factor compatibility. -/
  wildSign_eq : GloballyMinimalInput e → ∀ d : WildData, d.Valid e → rootNumber = wildSign e d

end VerifiedLcalc.Modularity
