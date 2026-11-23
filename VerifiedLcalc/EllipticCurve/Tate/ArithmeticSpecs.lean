/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.WildRootCore

/-! # Pure mathematical specifications for local arithmetic -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Negative j-valuation, guarding c4=0 rather than treating its valuation as zero. -/
def NegativeJValuation (e : (WeierstrassCurve ℤ)) (p : Nat) : Prop :=
  e.c₄ ≠ 0 ∧ 3 * (e.c₄).natAbs.factorization p < (e.Δ).natAbs.factorization p
  deriving Decidable

/-- The standard tame additive root formula, expressed using mathematical
factorization valuations and mathlib's Legendre symbol. -/
noncomputable def tameAdditiveRootSpec (e : (WeierstrassCurve ℤ)) (p : ℕ)
    [Fact p.Prime] : Int :=
  if NegativeJValuation e p then legendreSym p (-1)
  else
    let v := (e.Δ).natAbs.factorization p % 12
    if v = 3 ∨ v = 9 then legendreSym p (-2)
    else if v = 4 ∨ v = 8 then legendreSym p (-3)
    else legendreSym p (-1)

/-- Conductor exponents in the tame formulas: 0 at good reduction, 1 at a
multiplicative prime, 2 at an additive prime of residue characteristic >=5. -/
def tameConductorExponent (e : (WeierstrassCurve ℤ)) (p : ℕ) : ℕ :=
  if (WeierstrassCurve.baseChange e (ZMod p)).Δ ≠ 0 then 0
  else if (WeierstrassCurve.baseChange e (ZMod p)).c₄ ≠ 0 then 1 else 2

/-- Mathematical local root number, using the actual finite-field Frobenius trace. -/
noncomputable def tameLocalRootSpec (e : (WeierstrassCurve ℤ)) (p : ℕ)
    [Fact p.Prime] : Int :=
  if (WeierstrassCurve.baseChange e (ZMod p)).Δ ≠ 0 then 1
  else if (WeierstrassCurve.baseChange e (ZMod p)).c₄ ≠ 0 then
    -((WeierstrassCurve.baseChange e (ZMod p)).frobeniusTrace)
  else tameAdditiveRootSpec e p

/-- Mathematical conductor product for the tame formula. -/
noncomputable def tameLevel (e : (WeierstrassCurve ℤ)) : ℕ :=
  ∏ p ∈ (e.Δ).natAbs.primeFactors, p ^ tameConductorExponent e p

/-- Mathematical root number product for the tame formula. -/
noncomputable def tameSign (e : (WeierstrassCurve ℤ)) : Int :=
  -(∏ p ∈ (e.Δ).natAbs.primeFactors,
    if hp : p.Prime then @tameLocalRootSpec e p ⟨hp⟩ else 1)

/-- Valuation with the finite sentinel used at zero invariants. -/
def wildValuationSpec (p : Nat) (a : Int) : Nat :=
  if a = 0 then 12 else a.natAbs.factorization p

/-- Residue of the unit part of an integer at p. -/
def wildUnitSpec (p modulus : Nat) (a : Int) : Int :=
  (a / (p : Int)^(wildValuationSpec p a)) % (modulus : Int)

/-- Halberstadt's mathematical local sign from invariant valuations and a
checked Tate transcript, using Mathlib's characters. -/
noncomputable def wildRootSpec (e : (WeierstrassCurve ℤ)) (p : Nat)
    (w : TateWitness) : Int :=
  let c4 := e.c₄
  let c6 := e.c₆
  let delta := e.Δ
  let v4 := wildValuationSpec p c4
  let v6 := wildValuationSpec p c6
  let vd := wildValuationSpec p delta
  let modulus := if p = 2 then 64 else 81
  let u := wildUnitSpec p modulus c4
  let v := wildUnitSpec p modulus c6
  let d := wildUnitSpec p modulus delta
  if p = 2 then twoRootTable twoCharacter v4 v6 vd u v d w.kodaira
  else threeRootTable (legendreSym 3) v4 v6 vd u v d w.kodaira

/-- Mathematical conductor exponent using transcript offsets at wild primes. -/
noncomputable def wildExponentSpec (e : (WeierstrassCurve ℤ)) (d : WildData)
    (p : Nat) : Nat :=
  match (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | some w => e.Δ.natAbs.factorization p - w.offset
  | none => tameConductorExponent e p

/-- Mathematical local root number from invariant values and supplied wild data. -/
noncomputable def wildLocalRootSpec (e : (WeierstrassCurve ℤ)) (d : WildData) (p : Nat)
    [Fact p.Prime] : Int :=
  match (if p = 2 then d.atTwo else if p = 3 then d.atThree else none) with
  | some w => wildRootSpec e p w
  | none => tameLocalRootSpec e p

/-- Global conductor assembled from mathematical local exponents. -/
noncomputable def wildLevel (e : (WeierstrassCurve ℤ)) (d : WildData) : Nat :=
  ∏ p ∈ (e.Δ).natAbs.primeFactors, p^wildExponentSpec e d p

/-- Global root number assembled from mathematical local signs. -/
noncomputable def wildSign (e : (WeierstrassCurve ℤ)) (d : WildData) : Int :=
  -(∏ p ∈ (e.Δ).natAbs.primeFactors,
    if hp : p.Prime then @wildLocalRootSpec e d p ⟨hp⟩ else 1)

end VerifiedLcalc.EllipticCurve
