/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Tate.RationalLocalRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve

/-! # Mathematical specification of the checked Kodaira code -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open WeierstrassCurve

/-- The index of `Iₙ` in the PARI encoding. Code 1 represents `I₀`;
code `n + 4` represents `Iₙ` for positive `n`. -/
def kodairaIIndex (code : Int) : Option Nat :=
  if code = 1 then some 0
  else if 5 ≤ code then some (code - 4).toNat
  else none

/-- The exact `Iₙ` index, or exclusion of every `Iₙ` in the additive case. -/
def KodairaIndexSpec (W : WeierstrassCurve ℚ) [W.IsElliptic] (p : Nat)
    [Fact p.Prime] (index : Option Nat) : Prop :=
  match index with
  | some n => W.reductionSymbol (RationalLocalRing p) = .I n
  | none => ∀ n, W.reductionSymbol (RationalLocalRing p) ≠ .I n

/-- Interpret the multiplicative-family part of a PARI Kodaira code. -/
def KodairaCodeSpec (W : WeierstrassCurve ℚ) [W.IsElliptic] (p : Nat)
    [Fact p.Prime] (code : Int) : Prop :=
  KodairaIndexSpec W p (kodairaIIndex code)

end VerifiedLcalc.EllipticCurve
