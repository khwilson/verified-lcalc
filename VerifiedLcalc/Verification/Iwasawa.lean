/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Analytic

/-! # Exact consequences of normalized cyclotomic interpolation -/

@[expose] public section

namespace VerifiedLcalc

open Modularity IsDiscreteValuationRing

/-- The least coefficient valuation and its first occurrence are the two Iwasawa invariants. -/
theorem IwasawaSeriesOrder.correct {p : ℕ} [Fact p.Prime] {F : PowerSeries ℤ_[p]}
    (order : IwasawaSeriesOrder p F) :
    F.lambdaInvariant = order.lambda ∧ F.muInvariant = order.mu := by
  have mu : F.muInvariant = order.mu := le_antisymm
    (order.attained ▸ F.muInvariant_le_addVal_coeff order.lambda)
    (PowerSeries.le_muInvariant_iff.mpr order.lower)
  exact ⟨PowerSeries.lambdaInvariant_eq_iff.mpr
    ⟨order.attained.trans mu.symm, fun n hn => mu.symm ▸ order.earlier n hn⟩, mu⟩

/-- A unit augmentation gives a finite coefficient-order witness with both orders zero. -/
def IwasawaSeriesOrder.ofUnitConstantCoeff {p : ℕ} [Fact p.Prime] {F : PowerSeries ℤ_[p]}
    (h : IsUnit F.constantCoeff) : IwasawaSeriesOrder p F where
  lambda := 0
  mu := 0
  lower _ := zero_le
  attained := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact addVal_eq_zero_iff.mpr h
  earlier _ hn := (Nat.not_lt_zero _ hn).elim

variable {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
variable {symbols : IwasawaModularSymbols curve}

/-- Producer encoding of the provable row. Unknown markers carry no numerical data. -/
def IwasawaPrimeEvidence.encoding (row : IwasawaPrimeEvidence curve symbols) :
    Option (Sum String (List ℕ)) :=
  letI : Fact row.prime.val.Prime := ⟨row.prime.property⟩
  if row.additive.isSome then some (.inl "a")
  else
    match row.unsigned, row.signed with
    | some unsigned, _ => some (.inr [unsigned.order.lambda, unsigned.order.mu])
    | none, some signed => some (.inr [signed.plusOrder.lambda, signed.minusOrder.lambda,
        signed.plusOrder.mu])
    | none, none => none

/-- Retrieve the evidence for a selected prime from an attachment. -/
def IwasawaFacts.rowFor (facts : IwasawaFacts curve) (p : ℕ) :
    Option (IwasawaPrimeEvidence curve facts.symbols) :=
  facts.rows.find? (fun row => row.prime.val == p)

/-- Every good prime at or above the threshold has the stated vanishing, for the
actual normalized integral modular symbols. -/
theorem IwasawaThresholdEvidence.vanishing (h : IwasawaThresholdEvidence curve symbols)
    (p : Nat.Primes) (hle : h.prime.val ≤ p.val) (good : iwasawaGood curve p.val) :
    letI : Fact p.val.Prime := ⟨p.property⟩
    ∃ symbol : ℚ → ℤ_[p.val],
      (∀ r, (symbol r : ℚ_[p.val]) = (symbols.value r : ℚ_[p.val])) ∧
      GoodPrimeIwasawaVanishing curve symbol := by
  let : Fact p.val.Prime := ⟨p.property⟩
  obtain ⟨symbol, hsymbol, hinput⟩ := h.atGoodPrime p hle good
  exact ⟨symbol, hsymbol, hinput.vanishing (h.atLeastFive.trans hle)⟩

end VerifiedLcalc
