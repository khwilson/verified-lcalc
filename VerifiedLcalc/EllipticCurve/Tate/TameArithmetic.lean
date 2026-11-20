module

public import VerifiedLcalc.EllipticCurve.Tate.TameCore
public import VerifiedLcalc.EllipticCurve.BadPrime
public import VerifiedLcalc.EllipticCurve.Coefficients
public import Mathlib.NumberTheory.LegendreSymbol.Basic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open NumberField IsDedekindDomain

/-- The valuation-based mathematical condition for negative j-valuation.
The explicit c4 nonzero guard is essential at j=0. -/
def NegativeJValuation (e : (WeierstrassCurve ℤ)) (p : ℕ) : Prop :=
  e.c₄ ≠ 0 ∧ 3 * (e.c₄).natAbs.factorization p <
    (e.Δ).natAbs.factorization p
  deriving Decidable

theorem potentiallyMultiplicative_correct (e : (WeierstrassCurve ℤ)) (p : ℕ)
    (hp : p.Prime) : potentiallyMultiplicative e p = true ↔ NegativeJValuation e p := by
  simp only [potentiallyMultiplicative, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq, Nat.padicValNat_def, Nat.multiplicity_eq_factorization hp, NegativeJValuation]

/-- The standard tame additive formula, expressed using mathematical
factorization valuations and mathlib's Legendre symbol. Its arithmetic-to-
modular compatibility is an explicitly assumed standard theorem, not part of
this executable-correctness proof. -/
noncomputable def tameAdditiveRootSpec (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime] : Int :=
  if NegativeJValuation e p then legendreSym p (-1)
  else
    let v := (e.Δ).natAbs.factorization p % 12
    if v = 3 ∨ v = 9 then legendreSym p (-2)
    else if v = 4 ∨ v = 8 then legendreSym p (-3)
    else legendreSym p (-1)

theorem tameAdditiveRoot_correct (e : (WeierstrassCurve ℤ)) (p : ℕ)
    [Fact p.Prime] (hp : 3 < p) : tameAdditiveRoot e p = tameAdditiveRootSpec e p := by
  have hpot := potentiallyMultiplicative_correct e p (Fact.out : p.Prime)
  simp only [tameAdditiveRoot, dite_eq_left (Fact.out : p.Prime), tameAdditiveRootSpec,
    Nat.padicValNat_def, Nat.multiplicity_eq_factorization (Fact.out : p.Prime)]
  by_cases h : NegativeJValuation e p
  · rw [ite_eq_left h, ite_eq_left (hpot.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (mt hpot.mp h)]
    simp only [beq_iff_eq, Bool.or_eq_true]

/-- Conductor exponents in the tame formulas: 0 at good reduction, 1 at a
multiplicative prime, 2 at an additive prime of residue characteristic >=5. -/
def tameConductorExponent (e : (WeierstrassCurve ℤ)) (p : ℕ) : ℕ :=
  if (WeierstrassCurve.baseChange e (ZMod p)).Δ ≠ 0 then 0
  else if (WeierstrassCurve.baseChange e (ZMod p)).c₄ ≠ 0 then 1 else 2

noncomputable def tameLocalRootSpec (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime] : Int :=
  if (WeierstrassCurve.baseChange e (ZMod p)).Δ ≠ 0 then 1
  else if (WeierstrassCurve.baseChange e (ZMod p)).c₄ ≠ 0 then -(computeFrobeniusTrace e p)
  else tameAdditiveRootSpec e p

/-- Mathematical conductor product, evaluated only under minimality and no
additive reduction at 2 or 3 when connected to a modular realization. -/
noncomputable def tameLevel (e : (WeierstrassCurve ℤ)) : ℕ :=
  ∏ p ∈ (e.Δ).natAbs.primeFactors, p ^ tameConductorExponent e p

noncomputable def tameSign (e : (WeierstrassCurve ℤ)) : Int :=
  -(∏ p ∈ (e.Δ).natAbs.primeFactors,
    if hp : p.Prime then @tameLocalRootSpec e p ⟨hp⟩ else 1)

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc.EllipticCurve

theorem localExponent_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) :
    localExponent e p = tameConductorExponent e p := by
  unfold localExponent tameConductorExponent
  cases h : modelReduction e p with
  | good => simp [(modelReduction_good_iff e p).mp h]
  | multiplicative =>
    obtain ⟨hd, hc⟩ := (modelReduction_multiplicative_iff e p).mp h
    simp [hd, hc]
  | additive =>
    obtain ⟨hd, hc⟩ := (modelReduction_additive_iff e p).mp h
    simp [hd, hc]

theorem localRoot_correct (e : (WeierstrassCurve ℤ)) (p : ℕ) [Fact p.Prime]
    (hs : modelReduction e p ≠ .additive ∨ 3 < p) :
    localRoot e p = tameLocalRootSpec e p := by
  unfold localRoot tameLocalRootSpec
  cases h : modelReduction e p with
  | good => simp [(modelReduction_good_iff e p).mp h]
  | multiplicative =>
    obtain ⟨hd, hc⟩ := (modelReduction_multiplicative_iff e p).mp h
    have hg : goodReduction e p = false := by
      cases h' : goodReduction e p
      · rfl
      · exact False.elim (((goodReduction_correct e p).mp h') hd)
    simp [hd, hc, singularTrace_correct e p hg]
  | additive =>
    obtain ⟨hd, hc⟩ := (modelReduction_additive_iff e p).mp h
    have hp : 3 < p := hs.resolve_left (by simp [h])
    simp [hd, hc, tameAdditiveRoot_correct e p hp]

/-- Every returned local record is prime, supported, and agrees with the
mathematical conductor exponent and local sign formula. -/
theorem localConductorRoot?_correct (e : (WeierstrassCurve ℤ)) (p : ℕ)
    (d : LocalConductorRoot) (h : localConductorRoot? e p = some d) :
    ∃ hp : p.Prime, d.prime = p ∧
      (modelReduction e p ≠ .additive ∨ 3 < p) ∧
      d.exponent = tameConductorExponent e p ∧
      d.root = @tameLocalRootSpec e p ⟨hp⟩ := by
  have hp : p.Prime := by
    by_contra hn
    have hf : isPrime p = false := Bool.eq_false_iff.mpr (mt (isPrime_correct p).mp hn)
    simp [localConductorRoot?, hf] at h
  let : Fact p.Prime := ⟨hp⟩
  have ht : isPrime p = true := (isPrime_correct p).mpr hp
  have hs : modelReduction e p ≠ .additive ∨ 3 < p := by
    cases hr : modelReduction e p with
    | good => simp [hr]
    | multiplicative => simp [hr]
    | additive =>
      right
      by_contra hn
      simp [localConductorRoot?, ht, hr, hn] at h
  refine ⟨hp, ?_⟩
  have he : d = ⟨p, localExponent e p, localRoot e p⟩ := by
    cases hr : modelReduction e p <;>
      simp_all [localConductorRoot?, localExponent, localRoot]
  subst d
  exact ⟨rfl, hs, localExponent_correct e p, localRoot_correct e p hs⟩

theorem tameAtWild_correct (e : (WeierstrassCurve ℤ)) :
    tameAtWild e = true ↔
      modelReduction e 2 ≠ .additive ∧ modelReduction e 3 ≠ .additive := by
  simp [tameAtWild]

/-- Kernel-evaluable versions of the mathematical finite products. -/
noncomputable def tameLevelFast (e : (WeierstrassCurve ℤ)) : ℕ :=
  ∏ p ∈ (e.Δ).natAbs.primeFactors, p ^ localExponent e p
noncomputable def tameSignFast (e : (WeierstrassCurve ℤ)) : Int :=
  -(∏ p ∈ (e.Δ).natAbs.primeFactors, localRoot e p)

theorem tameLevel_eq_fast (e : (WeierstrassCurve ℤ)) : tameLevel e = tameLevelFast e := by
  simp only [tameLevel, tameLevelFast, localExponent_correct]

theorem tameSign_eq_fast (e : (WeierstrassCurve ℤ)) (hw : tameAtWild e = true) :
    tameSign e = tameSignFast e := by
  unfold tameSign tameSignFast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  let : Fact p.Prime := ⟨hprime⟩
  rw [dite_eq_left hprime]
  symm
  apply localRoot_correct
  by_cases h : 3 < p
  · exact Or.inr h
  · left
    have h23 : p = 2 ∨ p = 3 := by have := hprime.two_le; omega
    rcases (tameAtWild_correct e).mp hw with ⟨h2, h3⟩
    rcases h23 with rfl | rfl <;> assumption

/-- Aggregation preserves every checked local record. Prime-list completeness
is deliberately a separate global obligation. -/
theorem conductorRootFromPrimes?_correct (e : (WeierstrassCurve ℤ)) (ps : List Nat)
    (r : Nat × Int) (h : conductorRootFromPrimes? e ps = some r) :
    ∃ ds : List LocalConductorRoot,
      ps.mapM (localConductorRoot? e) = some ds ∧
      r = ((ds.map (fun d => d.prime ^ d.exponent)).prod, -(ds.map (·.root)).prod) := by
  unfold conductorRootFromPrimes? at h
  cases hd : ps.mapM (localConductorRoot? e) with
  | none => simp [hd] at h
  | some ds => exact ⟨ds, rfl, by simpa [hd] using h.symm⟩

end VerifiedLcalc.EllipticCurve
