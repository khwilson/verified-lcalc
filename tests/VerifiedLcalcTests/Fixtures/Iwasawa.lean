/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import VerifiedLcalc.EllipticCurve.Modularity.Realization
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.WorkedExamples.Reduced

/-! # Conditional interpolation checks for the LMFDB 11.a2 Iwasawa row

The explicit hypotheses provide normalized modular symbols and compatible
cyclotomic distributions. The finite and infinite conclusions use the
arithmetic augmentations, rather than hypotheses on lambda or mu.
-/

@[expose] public noncomputable section

namespace VerifiedLcalcTests.Iwasawa11

open VerifiedLcalc VerifiedLcalc.Modularity TauCeti.WorkedExamples

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The explicit analytic and arithmetic inputs for Cremona 11a1 at level eleven. -/
class Interpolation11 (level : outParam ℕ) where
  /-- Actual arithmetic realization and period-normalized modular symbols. -/
  symbols : IwasawaModularSymbols curve11a2
  /-- Level of the modular symbols. -/
  level_eq : symbols.realization.level = level
  /-- The modular curve of conductor eleven. -/
  atEleven : level = 11
  /-- Normalized ratio of the central value to the minimal real period. -/
  central : symbols.value 0 = 1 / 5
  /-- Integral embeddings of the rational modular symbols at three. -/
  symbol3 : ℚ → ℤ_[3]
  /-- Integral symbols at three are lifts of the actual rational values. -/
  symbol3_eq : ∀ r, (symbol3 r : ℚ_[3]) = (symbols.value r : ℚ_[3])
  /-- Local unit root at three. -/
  alpha3 : ℤ_[3]ˣ
  /-- The root satisfies the actual curve Euler polynomial. -/
  root3 : IsOrdinaryRoot curve11a2 alpha3
  /-- The ordinary cyclotomic series at three. -/
  series3 : PowerSeries ℤ_[3]
  /-- The full distribution at three is characterized by the finite levels. -/
  interpolation3 : OrdinarilyInterpolates symbol3 alpha3 series3
  /-- Level-zero symbol identity from the Hecke relation at three. -/
  initial3 : IwasawaLevelZeroIdentity curve11a2 symbol3
  /-- At every good prime at least seven, supply local distribution and Hecke inputs. -/
  large : ∀ (p : Nat.Primes), 7 ≤ p.val → iwasawaGood curve11a2 p.val →
    letI : Fact p.val.Prime := ⟨p.property⟩
    ∃ symbol : ℚ → ℤ_[p.val],
      (∀ r, (symbol r : ℚ_[p.val]) = (symbols.value r : ℚ_[p.val])) ∧
      GoodPrimeIwasawaInterpolation curve11a2 symbol

/-- An integral p-adic lift of one fifth is a unit. -/
theorem unit_lift_one_fifth {p : ℕ} [Fact p.Prime] {x : ℤ_[p]}
    (h : (x : ℚ_[p]) = ((1 / 5 : ℚ) : ℚ_[p])) : IsUnit x := by
  have hx : (5 : ℤ_[p]) * x = 1 := by
    apply Subtype.ext
    change ((5 : ℤ_[p]) : ℚ_[p]) * (x : ℚ_[p]) = 1
    rw [h]
    norm_num
  exact IsUnit.of_mul_eq_one_right (5 : ℤ_[p]) hx

/-- Three is nonanomalous by the checked arithmetic trace of the equation. -/
theorem nonanomalous3 (m : ModularRealization curve11a2) :
    (iwasawaTrace curve11a2 3 : ZMod 3) ≠ 1 := by
  have computed : EllipticCurve.computeFrobeniusTrace curve11a2 3 = -1 := by decide
  have qcoeff := m.goodPrimeCoefficients_computed 3 (by decide) (by decide)
  have h : (iwasawaTrace curve11a2 3 : ℂ) = (-1 : ℤ) := by
    rw [iwasawaTrace, ← m.coefficients, qcoeff, computed]
  have ht : iwasawaTrace curve11a2 3 = -1 := by exact_mod_cast h
  rw [ht]
  decide

/-- Build the supported row at three and the infinite threshold from augmentation inputs. -/
def facts {level : ℕ} (h : Interpolation11 level) : IwasawaFacts curve11a2 where
  symbols := h.symbols
  rows := [{
    prime := ⟨3, by decide⟩
    integralSymbol := h.symbol3
    symbol_eq := h.symbol3_eq
    unsigned := some {
      odd := by decide
      alpha := h.alpha3
      series := h.series3
      interpolation := Or.inl ⟨by decide, h.root3, h.interpolation3⟩
      order := IwasawaSeriesOrder.ofUnitConstantCoeff
        (h.interpolation3.unit_of_augmentation h.root3 h.initial3 (nonanomalous3 h.symbols.realization)
          (unit_lift_one_fifth ((h.symbol3_eq 0).trans (congrArg Rat.cast h.central)))) } }]
  threshold := some {
    prime := ⟨7, by decide⟩
    atLeastFive := by decide
    atGoodPrime p hp hg := by
      let : Fact p.val.Prime := ⟨p.property⟩
      obtain ⟨symbol, he, hi⟩ := h.large p hp hg
      exact ⟨symbol, he, unit_lift_one_fifth ((he 0).trans (congrArg Rat.cast h.central)), hi⟩ }

/-- Common proof attachment for the structured and native JSON inputs. -/
def proofs {level : ℕ} (h : Interpolation11 level) : IntegralCurveProofs curve11a2 where
  iwasawa := some (facts h)

section

variable {level : ℕ} [h : Interpolation11 level]

certify_ec Iwasawa11 from_json_string
  r#"{"ainvs":[0,-1,1,-10,-20],"iwdata":{"2":[0,1,0],"3":[0,0],"5":[0,0],"11":[1,0]},"iwp0":7}"#
  with_proofs (proofs h)

end

end VerifiedLcalcTests.Iwasawa11
