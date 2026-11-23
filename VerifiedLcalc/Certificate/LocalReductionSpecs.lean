/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.LocalClaims
public import VerifiedLcalc.EllipticCurve.Tate.LocalReduction
public import VerifiedLcalc.EllipticCurve.Tate.Tamagawa
public import VerifiedLcalc.EllipticCurve.Tate.Kodaira
public import VerifiedLcalc.EllipticCurve.GlobalCoefficients
public import Mathlib.RingTheory.Localization.Rat
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-! # Mathematical specifications for local row claims -/

@[expose] public section

namespace VerifiedLcalc
open EllipticCurve NumberField WeierstrassCurve

/-- Optional local claims on a minimal equation. The signed reduction code is
the trace of the singular reduction (zero for additive and ±1 for the two
multiplicative types). -/
def LocalReductionClaim.Spec (row : LocalReductionClaim) (e : WeierstrassCurve ℤ)
    [(e.baseChange ℚ).IsElliptic] : Prop :=
  ∃ hp : row.prime.Prime,
    letI : Fact row.prime.Prime := ⟨hp⟩
    let R := RationalLocalRing row.prime
    IsMinimal R (e.baseChange ℚ) ∧
    (∀ n, row.discriminantValuation = some n → e.Δ.natAbs.factorization row.prime = n) ∧
    (∀ n, row.jDenominatorValuation = some n →
      (e.baseChange ℚ).j.den.factorization row.prime = n) ∧
    (∀ k, row.reductionType = some k →
      ((e.baseChange ℚ).HasAdditiveReduction R ∧ k = 0 ∨
        (e.baseChange ℚ).HasMultiplicativeReduction R ∧
          (k = 1 ∧ (e.baseChange ℚ).HasSplitMultiplicativeReduction R ∨
           k = -1 ∧ ¬ (e.baseChange ℚ).HasSplitMultiplicativeReduction R)) ∧
      (e.baseChange (ZMod row.prime)).frobeniusTrace = k)
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

end VerifiedLcalc
