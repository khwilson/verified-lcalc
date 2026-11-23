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

/-- The canonical Tate symbol is the claimed `Iₙ`, or lies outside that family
when the code represents additive reduction. -/
def KodairaCodeSpec (W : WeierstrassCurve ℚ) [W.IsElliptic] (p : Nat)
    [Fact p.Prime] (code : Int) : Prop :=
  match kodairaIIndex code with
  | some n => W.reductionSymbol (RationalLocalRing p) = .I n
  | none => ∀ n, W.reductionSymbol (RationalLocalRing p) ≠ .I n

end VerifiedLcalc.EllipticCurve
