/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.LocalReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Localization
import TauCeti.Data.Nat.Prime.IntCast

/-! # Additive Tate terminal equations over rational local rings -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

open WeierstrassCurve IsDedekindDomain NumberField TauCeti

private theorem rationalPlace_asIdeal_span (p : ℕ) [Fact p.Prime] :
    (rationalPlace p).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  ext x
  change Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)} ↔ x ∈ Ideal.span {(p : 𝓞 ℚ)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  simpa only [map_natCast] using (map_dvd_iff Rat.ringOfIntegersEquiv (a := (p : 𝓞 ℚ))
    (b := x))

private theorem rationalLocalRing_maximalIdeal (p : ℕ) [Fact p.Prime] :
    IsLocalRing.maximalIdeal (RationalLocalRing p) = Ideal.span {(p : RationalLocalRing p)} := by
  let v := rationalPlace p
  let f := algebraMap (𝓞 ℚ) (RationalLocalRing p)
  calc
    _ = Ideal.map f v.asIdeal := (IsLocalization.AtPrime.map_eq_maximalIdeal
      v.asIdeal (RationalLocalRing p)).symm
    _ = Ideal.map f (Ideal.span {(p : 𝓞 ℚ)}) :=
      congrArg (Ideal.map f) (rationalPlace_asIdeal_span p)
    _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- The rational prime is a uniformizer in its local ring. -/
theorem rationalLocalRing_irreducible_natCast (p : ℕ) [Fact p.Prime] :
    Irreducible (p : RationalLocalRing p) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (rationalLocalRing_maximalIdeal p)

/-- The rational prime remains a uniformizer on passing to the completed integers. -/
theorem rationalCompletion_irreducible_natCast (p : ℕ) [Fact p.Prime] :
    Irreducible (p : (rationalPlace p).adicCompletionIntegers ℚ) := by
  let v := rationalPlace p
  simpa only [map_natCast] using (v.irreducible_localizationToCompletionIntegers_iff (K := ℚ)).mpr
    (rationalLocalRing_irreducible_natCast p)

/-- A terminal test over the integers holds over any discrete valuation ring
with the same prime number as uniformizer. -/
theorem isTateTerminal_baseChange_int {R : Type*} [CommRing R] [IsDomain R]
    (e : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hϖ : Irreducible (p : R)) {symbol : ReductionSymbol}
    (h : e.IsTateTerminal (p : ℤ) symbol) :
    (e.baseChange R).IsTateTerminal (p : R) symbol := by
  let f := Int.castRingHom R
  have hdvd := (Fact.out : p.Prime).pow_dvd_intCast_iff
    (.of_ne_zero hϖ.ne_zero) hϖ.not_isUnit
  change (e.map f).IsTateTerminal (p : R) symbol
  rw [← map_natCast f p, isTateTerminal_map_iff _ fun n x => by simpa [f] using hdvd n x]
  exact h

/-- An integral variable change followed by a valid terminal test identifies
the intrinsic Kodaira symbol. -/
theorem reductionSymbol_eq_of_int_terminal {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (e : WeierstrassCurve ℤ) [(e.baseChange K).IsElliptic] (p : ℕ) [Fact p.Prime]
    (hϖ : Irreducible (p : R)) (changeOfVariables : VariableChange ℤ) {symbol : ReductionSymbol}
    (h : (changeOfVariables • e).IsTateTerminal (p : ℤ) symbol) :
    (e.baseChange K).reductionSymbol R = symbol := by
  have heq : changeOfVariables.baseChange K • e.baseChange K =
      ((changeOfVariables • e).baseChange R).baseChange K := by
    simp only [WeierstrassCurve.baseChange, VariableChange.baseChange, map_variableChange, map_map]
    congr 1
    exact Subsingleton.elim _ _
  exact reductionSymbol_eq_of_isTateTerminal _ heq hϖ (isTateTerminal_baseChange_int _ p hϖ h)

/-- The positive starred case needs only the stage index determined by parity. -/
def isTateTerminal_IStar_succ_decidable (e : WeierstrassCurve ℤ) (p : ℤ) (n : ℕ) :
    Decidable (e.IsTateTerminal p (.IStar (n + 1))) := by
  let k := n / 2
  let oddStage (i : ℕ) := IsTateOddStage p i e ∧ ¬ p ^ (2 * i + 5) ∣ e.b₆
  let evenStage (i : ℕ) := IsTateEvenStage p i e ∧ ¬ p ^ (2 * i + 7) ∣ discrim e.a₂ e.a₄ e.a₆
  let test := (n = 2 * k ∧ oddStage k) ∨ (n = 2 * k + 1 ∧ evenStage k)
  let : Decidable (IsTateOddStage p k e) := decidable_of_iff _ isTateOddStage_iff.symm
  let : Decidable (IsTateEvenStage p k e) := decidable_of_iff _ isTateEvenStage_iff.symm
  let : Decidable test := inferInstanceAs (Decidable
    ((n = 2 * k ∧ (IsTateOddStage p k e ∧ ¬ p ^ (2 * k + 5) ∣ e.b₆)) ∨
      (n = 2 * k + 1 ∧ (IsTateEvenStage p k e ∧ ¬ p ^ (2 * k + 7) ∣ discrim e.a₂ e.a₄ e.a₆))))
  refine decidable_of_iff test (Iff.trans ?_ isTateTerminal_IStar_add_one.symm)
  change test ↔ (∃ i, n = 2 * i ∧ oddStage i) ∨ (∃ i, n = 2 * i + 1 ∧ evenStage i)
  constructor
  · rintro (⟨hi, h⟩ | ⟨hi, h⟩)
    · exact Or.inl ⟨k, hi, h⟩
    · exact Or.inr ⟨k, hi, h⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · have hk : i = k := by
        dsimp [k]
        omega
      exact Or.inl ⟨hk ▸ hi, hk ▸ h⟩
    · have hk : i = k := by
        dsimp [k]
        omega
      exact Or.inr ⟨hk ▸ hi, hk ▸ h⟩

/-- Tate's stopping predicate on an integer equation is a finite test. -/
def decidableIsTateTerminalInt (e : WeierstrassCurve ℤ) (p : ℤ)
    (symbol : ReductionSymbol) : Decidable (e.IsTateTerminal p symbol) := by
  rcases symbol with (_ | n) | _ | _ | _ | (_ | n) | _ | _ | _
  case I.zero => exact decidable_of_iff _ isTateTerminal_I_zero.symm
  case I.succ => exact decidable_of_iff _ isTateTerminal_I_add_one.symm
  case II => exact decidable_of_iff _ isTateTerminal_II.symm
  case III => exact decidable_of_iff _ isTateTerminal_III.symm
  case IV => exact decidable_of_iff _ isTateTerminal_IV.symm
  case IStar.zero => exact decidable_of_iff _ isTateTerminal_IStar_zero.symm
  case IStar.succ => exact isTateTerminal_IStar_succ_decidable e p n
  case IVStar => exact decidable_of_iff _ isTateTerminal_IVStar.symm
  case IIIStar => exact decidable_of_iff _ isTateTerminal_IIIStar.symm
  case IIStar => exact decidable_of_iff _ isTateTerminal_IIStar.symm

/-- A canonical reduction symbol in the additive family. -/
abbrev AdditiveReductionSymbol := { symbol : ReductionSymbol // ∀ n, symbol ≠ .I n }

/-- Decode the additive cases of the PARI Kodaira code convention. -/
def additiveKodairaSymbol : ℤ → Option AdditiveReductionSymbol
  | 2 => some ⟨.II, fun _ h => ReductionSymbol.noConfusion h⟩
  | 3 => some ⟨.III, fun _ h => ReductionSymbol.noConfusion h⟩
  | 4 => some ⟨.IV, fun _ h => ReductionSymbol.noConfusion h⟩
  | -1 => some ⟨.IStar 0, fun _ h => ReductionSymbol.noConfusion h⟩
  | -2 => some ⟨.IIStar, fun _ h => ReductionSymbol.noConfusion h⟩
  | -3 => some ⟨.IIIStar, fun _ h => ReductionSymbol.noConfusion h⟩
  | -4 => some ⟨.IVStar, fun _ h => ReductionSymbol.noConfusion h⟩
  | code =>
    if code ≤ -5 then
      some ⟨.IStar (-code - 4).toNat, fun _ h => ReductionSymbol.noConfusion h⟩
    else none

/-- The integral translation `(r,s,t)` supplied with a terminal claim. -/
def intTateTranslation (rst : ℤ × ℤ × ℤ) : VariableChange ℤ :=
  ⟨1, rst.1, rst.2.1, rst.2.2⟩

/-- A checked integral translation to an additive terminal equation of the same curve. -/
structure AdditiveTerminalFact (curve : WeierstrassCurve ℤ) (prime : Nat.Primes) where
  /-- The integral translation applied before running the terminal test. -/
  translation : ℤ × ℤ × ℤ
  /-- The canonical additive symbol recorded in the terminal test. -/
  symbol : AdditiveReductionSymbol
  /-- The translated model satisfies the actual stopping criterion. -/
  terminal :
    (intTateTranslation translation • curve).IsTateTerminal ((prime : ℕ) : ℤ) symbol.val

/-- The checked terminal equation identifies the actual local Kodaira symbol. -/
theorem AdditiveTerminalFact.reductionSymbol_eq {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] {prime : Nat.Primes}
    (fact : AdditiveTerminalFact curve prime) :
    letI : Fact (prime : ℕ).Prime := ⟨prime.prop⟩
    (curve.baseChange ℚ).reductionSymbol (RationalLocalRing (prime : ℕ)) = fact.symbol.val := by
  let : Fact (prime : ℕ).Prime := ⟨prime.prop⟩
  exact reductionSymbol_eq_of_int_terminal curve prime
    (rationalLocalRing_irreducible_natCast prime) _ fact.terminal

end VerifiedLcalc.EllipticCurve
