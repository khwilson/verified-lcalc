/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.EllipticCurve.Tate.RationalLocalRing
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.RingTheory.Localization.AtPrime
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

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
    letI : IsDiscreteValuationRing R :=
      IsDedekindDomain.HeightOneSpectrum.isDiscreteValuationRing_localizationAtPrime
        (rationalPlace row.prime)
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
end VerifiedLcalc
