/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Data.ZMod.Basic
public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.EllipticCurve.BadPrimeCore

/-! # Executable support conditions for intrinsic local Tamagawa factors -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- The exact Tamagawa factor is supported at good reduction and at
multiplicative reduction of index one. -/
def supportsTamagawaOne (e : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  decide (¬ (p : ℤ) ∣ e.Δ) ||
    decide ((p : ℤ) ∣ e.Δ ∧ ¬ (p : ℤ) ^ 2 ∣ e.Δ ∧ ¬ (p : ℤ) ∣ e.c₄)

/-- The integral model has discriminant valuation two and unit c₄ at the given prime. -/
def multiplicativeIndexTwo (e : WeierstrassCurve ℤ) (p : ℕ) : Bool :=
  decide ((p : ℤ) ^ 2 ∣ e.Δ ∧ ¬ (p : ℤ) ^ 3 ∣ e.Δ ∧ ¬ (p : ℤ) ∣ e.c₄)

/-- Interpret the submitted coordinates as an integral change with scale one. -/
def typeIIIChange (shift : TamagawaTypeIIIShift) : WeierstrassCurve.VariableChange ℤ :=
  ⟨1, shift.r, shift.s, shift.t⟩

/-- Interpret the submitted type IV coordinates as a unit-scale translation. -/
def typeIVChange (evidence : TamagawaTypeIVEvidence) : WeierstrassCurve.VariableChange ℤ :=
  ⟨1, evidence.r, evidence.s, evidence.t⟩

/-- Check supplied splitting evidence for the original multiplicative node polynomial. -/
def checkTamagawaSplitting (e : WeierstrassCurve ℤ) (p : ℕ)
    (evidence : TamagawaSplittingEvidence) : Bool :=
  match evidence with
  | .root value => decide (2 < p ∧ value < p ∧
      nodeValue e value % (p : ℤ) = 0)
  | .nonsplitEulerPower value =>
    let nodeDiscriminant : ZMod p := (-(e.c₄ * e.c₆) : ℤ)
    decide (2 < p ∧ value + 1 = p ∧
      nodeDiscriminant ^ ((p - 1) / 2) = -1)

/-- The factor determined by supplied splitting evidence and the discriminant index. -/
def multiplicativeTamagawaFactor (e : WeierstrassCurve ℤ) (p : ℕ)
    (evidence : TamagawaSplittingEvidence) : ℕ :=
  let index := padicValNat p e.Δ.natAbs
  match evidence with
  | .root _ => index
  | .nonsplitEulerPower _ => Nat.gcd 2 index

/-- The level-one residue quadratic attached to a submitted terminal model. -/
def typeIVResiduePolynomial (model : WeierstrassCurve ℤ) (p : ℕ) (y : ZMod p) : ZMod p :=
  y ^ 2 + ((model.a₃ / (p : ℤ) : ℤ) : ZMod p) * y -
    ((model.a₆ / (p : ℤ) ^ 2 : ℤ) : ZMod p)

/-- Check the terminal type III divisibilities for the exact submitted change of variables. -/
def checkTameTypeIII (e : WeierstrassCurve ℤ) (p : ℕ) (shift : TamagawaTypeIIIShift) : Bool :=
  let model := typeIIIChange shift • e
  decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ^ 2 ∣ model.a₆ ∧ ¬ (p : ℤ) ^ 3 ∣ model.b₈)

/-- Check the exact submitted type IV change, its terminal conditions, and its
tagged residue evidence. This checker evaluates no finite-field search. -/
def checkTameTypeIV (e : WeierstrassCurve ℤ) (p : ℕ)
    (evidence : TamagawaTypeIVEvidence) : Bool :=
  let model := typeIVChange evidence • e
  let terminal := decide (3 < p ∧ (p : ℤ) ∣ model.b₂ ∧ (p : ℤ) ∣ model.a₃ ∧
    (p : ℤ) ∣ model.a₄ ∧ (p : ℤ) ^ 2 ∣ model.a₆ ∧
    (p : ℤ) ^ 3 ∣ model.b₈ ∧ ¬ (p : ℤ) ^ 3 ∣ model.b₆)
  terminal && match evidence.residue with
  | .root y => decide (y < p ∧ typeIVResiduePolynomial model p (y : ZMod p) = 0)
  | .nonsplitEulerPower value => decide (value + 1 = p ∧
      (((model.a₃ / (p : ℤ)) ^ 2 + 4 * (model.a₆ / (p : ℤ) ^ 2) : ℤ) : ZMod p) ^
        ((p - 1) / 2) = -1)

/-- Check the supported Tamagawa route for the supplied evidence, if any. -/
def tamagawaExpected? (e : WeierstrassCurve ℤ) (p : ℕ)
    (shift : Option TamagawaTypeIIIShift := none)
    (typeIV : Option TamagawaTypeIVEvidence := none)
    (splitting : Option TamagawaSplittingEvidence := none) : Option ℕ :=
  match shift, typeIV, splitting with
  | some _, some _, _ | some _, _, some _ | _, some _, some _ => none
  | some change, none, none => if checkTameTypeIII e p change then some 2 else none
  | none, some evidence, none => if checkTameTypeIV e p evidence then
      some (match evidence.residue with | .root _ => 3 | .nonsplitEulerPower _ => 1)
    else none
  | none, none, some evidence =>
    if supportsTamagawaOne e p || multiplicativeIndexTwo e p then none
    else if (p : ℤ) ∣ e.c₄ then none
    else if checkTamagawaSplitting e p evidence then
      some (multiplicativeTamagawaFactor e p evidence)
    else none
  | none, none, none =>
    if supportsTamagawaOne e p then some 1
    else if multiplicativeIndexTwo e p then some 2
    else none

end VerifiedLcalc.EllipticCurve
