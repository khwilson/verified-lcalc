/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.EllipticCurve.Tate.TamagawaSpecs
public import VerifiedLcalc.EllipticCurve.Tate.KodairaSpecs
public import VerifiedLcalc.EllipticCurve.Tate.ArithmeticSpecs
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product

/-! # Specifications for local Tamagawa and Kodaira claims -/

@[expose] public section
namespace VerifiedLcalc
open EllipticCurve NumberField WeierstrassCurve

/-- Exact local Tamagawa data at the supported primes of the supplied equation. -/
def LocalReductionClaim.TamagawaSpec (row : LocalReductionClaim) (e : WeierstrassCurve ℤ) :
    Prop :=
  ∀ n, row.tamagawaNumber = some n → ∃ hp : row.prime.Prime,
    letI : Fact row.prime.Prime := ⟨hp⟩
    supportsTamagawaOne e row.prime = true →
      (e.baseChange ℚ).tamagawaNumberAt (rationalPlace row.prime) = n

/-- Exact canonical symbol for a good or multiplicative code, or exclusion of
the multiplicative family for an additive code. -/
def LocalReductionClaim.KodairaSpec (row : LocalReductionClaim) (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] : Prop :=
  ∃ hp : row.prime.Prime,
    letI : Fact row.prime.Prime := ⟨hp⟩
    ∀ code, row.kodairaSymbol = some code → KodairaCodeSpec (e.baseChange ℚ) row.prime code

/-- The supplied sign agrees with the local arithmetic formula at the checked prime. -/
def LocalReductionClaim.RootNumberSpec (row : LocalReductionClaim)
    (e : WeierstrassCurve ℤ) (d : WildData) : Prop :=
  ∀ value, row.rootNumber = some value → ∃ hp : row.prime.Prime,
    letI : Fact row.prime.Prime := ⟨hp⟩
    (value = 1 ∨ value = -1) ∧ wildLocalRootSpec e d row.prime = value

end VerifiedLcalc
