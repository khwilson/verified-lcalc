module
public import VerifiedLcalc.EllipticCurve.WildRootCore
public import VerifiedLcalc.EllipticCurve.TameArithmetic
public import VerifiedLcalc.EllipticCurve.InvariantMinimality
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open Artifacts

/-- Every transcript translation is mathlib's genuine integral variable change. -/
theorem translateIntegral_correct (e : CurveEquation) (r s t : Int) :
    weierstrass (translateIntegral e r s t) Int =
      (⟨1,r,s,t⟩ : WeierstrassCurve.VariableChange Int) • weierstrass e Int := by
  ext <;> simp [translateIntegral, weierstrass,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]

theorem translateIntegral_discriminant (e : CurveEquation) (r s t : Int) :
    discriminant (translateIntegral e r s t) = discriminant e := by
  rw [discriminant_correct, translateIntegral_correct, WeierstrassCurve.variableChange_Δ]
  simp [discriminant_correct]

theorem tateDiv_correct (p k : Nat) (a : Int) :
    TateDiv p k a ↔ (p : Int)^k ∣ a := Int.dvd_iff_emod_eq_zero.symm

theorem cubicRepeated_correct (p : Nat) (a b c x : Int) :
    cubicRepeated p a b c x ↔
      ((x : ZMod p)^3 + (a : ZMod p)*x^2 + (b : ZMod p)*x + c = 0 ∧
       3*(x : ZMod p)^2 + 2*(a : ZMod p)*x + b = 0) := by
  simp only [cubicRepeated, ← Int.dvd_iff_emod_eq_zero,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

theorem quadraticRepeated_correct (p : Nat) (a b c x : Int) :
    quadraticRepeated p a b c x ↔
      ((a : ZMod p)*x^2 + (b : ZMod p)*x + c = 0 ∧ 2*(a : ZMod p)*x + b = 0) := by
  simp only [quadraticRepeated, ← Int.dvd_iff_emod_eq_zero,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- The table uses mathlib's primitive characters of conductor 4 and 8. -/
def twoCharacterSpec (a n : Int) : Int :=
  if a = -1 then ZMod.χ₄ n
  else if a = 2 then ZMod.χ₈ n
  else if a = -2 then ZMod.χ₈' n else 0

theorem twoCharacter_correct (a n : Int) : twoCharacter a n = twoCharacterSpec a n := by
  unfold twoCharacter twoCharacterSpec
  simp only [ZMod.χ₄_int_eq_if_mod_four, ZMod.χ₈_int_eq_if_mod_eight,
    ZMod.χ₈'_int_eq_if_mod_eight]
  have h2 : n % 2 = (n % 8) % 2 := by omega
  have h4 : n % 4 = (n % 8) % 4 := by omega
  rw [h2, h4]
  by_cases h : n % 2 = 0 <;> simp [← h2, ← h4, h]

def wildValuationSpec (p : Nat) (a : Int) : Nat :=
  if a = 0 then 12 else a.natAbs.factorization p

def wildUnitSpec (p modulus : Nat) (a : Int) : Int :=
  (a / (p : Int)^(wildValuationSpec p a)) % (modulus : Int)

theorem wildValuation_correct (p : Nat) (hp : p.Prime) (a : Int) :
    wildValuation p a = wildValuationSpec p a := by
  simp [wildValuation, wildValuationSpec, primeExponent_correct hp]

theorem wildUnit_correct (p : Nat) (hp : p.Prime) (modulus : Nat) (a : Int) :
    wildUnit p modulus a = wildUnitSpec p modulus a := by
  simp [wildUnit, wildUnitSpec, wildValuation_correct p hp]

/-- Published Halberstadt table with mathematical factorization valuations,
actual curve invariants, mathlib characters, and mathlib's Legendre symbol.
Its geometric interpretation is the explicitly assumed compatibility theorem. -/
noncomputable def wildRootSpec (e : CurveEquation) (p : Nat) (w : TateWitness) : Int :=
  let c4 := (weierstrass e Int).c₄
  let c6 := (weierstrass e Int).c₆
  let delta := (weierstrass e Int).Δ
  let v4 := wildValuationSpec p c4
  let v6 := wildValuationSpec p c6
  let vd := wildValuationSpec p delta
  let modulus := if p = 2 then 64 else 81
  let u := wildUnitSpec p modulus c4
  let v := wildUnitSpec p modulus c6
  let d := wildUnitSpec p modulus delta
  if p = 2 then twoRootTable twoCharacterSpec v4 v6 vd u v d w.kodaira
  else threeRootTable (legendreSym 3) v4 v6 vd u v d w.kodaira

theorem wildRoot_correct (e : CurveEquation) (p : Nat) (hp : p.Prime) (w : TateWitness) :
    wildRoot e p w = wildRootSpec e p w := by
  have hK : twoCharacter = twoCharacterSpec := funext fun a => funext (twoCharacter_correct a)
  have h3 : legendreValue 3 = legendreSym 3 := funext (legendreValue_correct 3 (by decide))
  simp only [wildRoot, wildRootSpec, wildValuation_correct p hp, wildUnit_correct p hp,
    modelC4_correct, modelC6_correct, discriminant_correct, hK, h3]

/-- The actual reduction and valuation meaning of an executable Tate witness. -/
def TateWitness.ArithmeticSpec (w : TateWitness) (e : CurveEquation) (p : Nat) : Prop :=
  (p = 2 ∨ p = 3) ∧ (weierstrass e Int).Δ ≠ 0 ∧
    ((weierstrass e (ZMod p)).Δ = 0 ∧ (weierstrass e (ZMod p)).c₄ = 0) ∧
    w.Path e p ∧ w.offset < (weierstrass e Int).Δ.natAbs.factorization p

theorem tateWitness_valid_correct (w : TateWitness) (e : CurveEquation) (p : Nat) :
    w.Valid e p ↔ w.ArithmeticSpec e p := by
  unfold TateWitness.Valid TateWitness.ArithmeticSpec
  constructor
  · rintro ⟨hp, hn, hr, hw, ho⟩
    have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
    exact ⟨hp, hn, (modelReduction_additive_iff e p).mp hr, hw,
      by simpa only [primeExponent_correct hprime, discriminant_correct] using ho⟩
  · rintro ⟨hp, hn, hr, hw, ho⟩
    have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
    exact ⟨hp, hn, (modelReduction_additive_iff e p).mpr hr, hw,
      by simpa only [primeExponent_correct hprime, discriminant_correct] using ho⟩

noncomputable def wildExponentSpec (e : CurveEquation) (d : WildData) (p : Nat) : Nat :=
  match (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | some w => (weierstrass e Int).Δ.natAbs.factorization p - w.offset
  | none => tameConductorExponent e p

noncomputable def wildLocalRootSpec (e : CurveEquation) (d : WildData) (p : Nat) [Fact p.Prime] : Int :=
  match (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | some w => wildRootSpec e p w
  | none => tameLocalRootSpec e p

theorem wildExponent_correct (e : CurveEquation) (d : WildData) (p : Nat) (hp : p.Prime) :
    wildExponent e d p = wildExponentSpec e d p := by
  simp only [wildExponent, wildExponentSpec, primeExponent_correct hp,
    discriminant_correct, localExponent_correct]
  rfl

private theorem fallback_supported (e : CurveEquation) (d : WildData) (hd : d.Valid e)
    (p : Nat) (hp : p.Prime)
    (hn : (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) = none) :
    modelReduction e p ≠ .additive ∨ 3 < p := by
  by_cases h : 3 < p
  · exact Or.inr h
  left
  have h23 : p = 2 ∨ p = 3 := by have := hp.two_le; omega
  rcases h23 with rfl | rfl
  · simp only [ite_true] at hn
    have ht := hd.1
    rw [validWildAt, hn] at ht
    intro ha
    simp [ha] at ht
  · simp only [show (3 : Nat) ≠ 2 by decide, ite_false, ite_true] at hn
    have ht := hd.2
    rw [validWildAt, hn] at ht
    intro ha
    simp [ha] at ht

theorem wildLocalRoot_correct (e : CurveEquation) (d : WildData) (hd : d.Valid e)
    (p : Nat) [Fact p.Prime] : wildLocalRoot e d p = wildLocalRootSpec e d p := by
  unfold wildLocalRoot wildLocalRootSpec
  cases h : (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | none => exact localRoot_correct e p (fallback_supported e d hd p Fact.out h)
  | some w => exact wildRoot_correct e p Fact.out w

noncomputable def wildLevel (e : CurveEquation) (d : WildData) : Nat :=
  ∏ p ∈ (discriminant e).natAbs.primeFactors, p^wildExponentSpec e d p
noncomputable def wildSign (e : CurveEquation) (d : WildData) : Int :=
  -(∏ p ∈ (discriminant e).natAbs.primeFactors,
    if hp : p.Prime then @wildLocalRootSpec e d p ⟨hp⟩ else 1)
noncomputable def wildLevelFast (e : CurveEquation) (d : WildData) : Nat :=
  ∏ p ∈ (discriminant e).natAbs.primeFactors, p^wildExponent e d p
noncomputable def wildSignFast (e : CurveEquation) (d : WildData) : Int :=
  -(∏ p ∈ (discriminant e).natAbs.primeFactors, wildLocalRoot e d p)

theorem wildLevel_eq_fast (e : CurveEquation) (d : WildData) : wildLevel e d = wildLevelFast e d := by
  unfold wildLevel wildLevelFast
  apply Finset.prod_congr rfl
  intro p hp
  rw [wildExponent_correct e d p (Nat.mem_primeFactors.mp hp).1]

theorem wildSign_eq_fast (e : CurveEquation) (d : WildData) (hd : d.Valid e) :
    wildSign e d = wildSignFast e d := by
  unfold wildSign wildSignFast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (Nat.mem_primeFactors.mp hp).1
  let : Fact p.Prime := ⟨hprime⟩
  rw [dite_eq_left hprime, wildLocalRoot_correct e d hd p]


/-- Accepted optional data expose actual additive reduction, a checked Tate
path, and the mathematical Halberstadt sign, not just a producer assertion. -/
theorem validWildAt_some_spec (e : CurveEquation) (p : Nat) (w : TateWitness)
    (h : validWildAt e p (some w)) :
    w.ArithmeticSpec e p ∧ (wildRootSpec e p w = 1 ∨ wildRootSpec e p w = -1) := by
  have ha : modelReduction e p = .additive := by
    by_contra hn
    simp [validWildAt, hn] at h
  have hw : w.Valid e p ∧ (wildRoot e p w = 1 ∨ wildRoot e p w = -1) := by
    simpa [validWildAt, ha] using h
  have hp : p.Prime := by rcases hw.1.1 with rfl | rfl <;> decide
  exact ⟨(tateWitness_valid_correct w e p).mp hw.1,
    by simpa only [wildRoot_correct e p hp w] using hw.2⟩

noncomputable def wildConductorRootFromPrimesSpec (e : CurveEquation) (d : WildData)
    (ps : List Nat) : Nat × Int :=
  ((ps.map fun p => p^wildExponentSpec e d p).prod,
    -(ps.map fun p => if hp : p.Prime then @wildLocalRootSpec e d p ⟨hp⟩ else 1).prod)

/-- Candidate aggregation agrees with mathematical local formulas on every
prime in the list. Completeness is checked against the global product later. -/
theorem wildConductorRootFromPrimes_correct (e : CurveEquation) (d : WildData)
    (hd : d.Valid e) (ps : List Nat) (hp : ∀ p ∈ ps, p.Prime) :
    wildConductorRootFromPrimes e d ps = wildConductorRootFromPrimesSpec e d ps := by
  apply Prod.ext
  · change (ps.map _).prod = (ps.map _).prod
    congr 1
    apply List.map_congr_left
    intro p hmem
    rw [wildExponent_correct e d p (hp p hmem)]
  · change -(ps.map _).prod = -(ps.map _).prod
    congr 2
    apply List.map_congr_left
    intro p hmem
    have hprime := hp p hmem
    let : Fact p.Prime := ⟨hprime⟩
    rw [dite_eq_left hprime, wildLocalRoot_correct e d hd p]

end VerifiedLcalc.EllipticCurve
