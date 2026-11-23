/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.RealizationData
public import VerifiedLcalc.EllipticCurve.Tate.ArithmeticSpecs
public import VerifiedLcalc.EllipticCurve.Tate.TameCore
public import TauCeti.AlgebraicGeometry.EllipticCurve.GlobalMinimalModel

/-! # Arithmetic compatibility fields for a modular realization -/

@[expose] public section
namespace VerifiedLcalc.Modularity
open EllipticCurve NumberField

/-- General modularity with standard arithmetic compatibility. The local
arithmetic identifications below are the authorized temporary compatibility
assumption, stated using the mathematical formulas in `Tate.ArithmeticSpecs`. -/
structure ArithmeticModularRealization (e : (WeierstrassCurve ℤ))
    extends ModularRealization e where
  /-- Tame conductor compatibility, under global minimality and tame support. -/
  tameLevel_eq : ∀ [(e.baseChange ℚ).IsElliptic],
    WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ) →
      tameAtWild e = true → level = tameLevel e
  /-- Tame root-number compatibility, under global minimality and tame support. -/
  tameSign_eq : ∀ [(e.baseChange ℚ).IsElliptic],
    WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ) →
      tameAtWild e = true → rootNumber = tameSign e
  /-- Standard Tate/Ogg arithmetic-conductor compatibility. -/
  wildLevel_eq : ∀ [(e.baseChange ℚ).IsElliptic],
    WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ) →
      ∀ d : WildData, d.Valid e → level = wildLevel e d
  /-- Standard Halberstadt local-epsilon-factor compatibility. -/
  wildSign_eq : ∀ [(e.baseChange ℚ).IsElliptic],
    WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ) →
      ∀ d : WildData, d.Valid e → rootNumber = wildSign e d

end VerifiedLcalc.Modularity
