/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.AdelicImageSpecs
public import VerifiedLcalc.Certificate.ResidualImageLabels

/-! # Native labels for integral-prime and finite torsion images

The prime-adic rows specify a prime, a truncation depth, and generators in the
truncated general linear group. The modular-curve rows use the LMFDB finite
subgroup convention at the level in the label.
-/

@[expose] public section

namespace VerifiedLcalc

/-- Integral-prime matrix reduction at the specified depth. -/
noncomputable def localImageReduction (p : Nat.Primes) (depth : ℕ) :
    Matrix.GeneralLinearGroup (Fin 2) (AdelicLocalRing p) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod (p.val ^ depth)) :=
  letI : Fact p.val.Prime := ⟨p.property⟩
  Matrix.GeneralLinearGroup.map (PadicInt.toZModPow depth)

/-- Selected representatives from the Rouse–Sutherland–Zureick-Brown prime-adic
catalogue, normalized to least nonnegative entries. The final component gives
the generators modulo the prime to the specified depth. -/
def padicImageReference : String → Option (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ))
  | "2.2.0.1" => some (2, 1, [(1, 1, 1, 0)])
  | "2.3.0.1" => some (2, 1, [(1, 1, 0, 1)])
  | "2.6.0.1" => some (2, 1, [])
  | "4.2.0.1" => some (2, 2, [(1, 3, 1, 0), (1, 2, 1, 1)])
  | "4.4.0.1" => some (2, 2, [(2, 3, 1, 2), (3, 1, 3, 2)])
  | "8.12.0.1" => some (2, 3, [(3, 6, 2, 1), (3, 0, 6, 5), (3, 2, 0, 1), (5, 4, 2, 7)])
  | "5.24.0.1" => some (5, 1, [(1, 1, 0, 1), (1, 1, 0, 3)])
  | "5.120.0.1" => some (5, 1, [(2, 0, 0, 1)])
  | "25.120.0.1" => some (5, 2, [(6, 9, 0, 11), (6, 13, 0, 18)])
  | "25.120.0.2" => some (5, 2, [(24, 19, 0, 23), (6, 21, 0, 19)])
  | "25.120.0.3" => some (5, 2, [(8, 18, 0, 21), (21, 21, 0, 11)])
  | _ => none

/-- Selected native modular-curve labels. At level two the classes have order
two and order one. The level-22 matrices come from the adelic row of 64064.o1. -/
def finiteImageReference : String → Option (ℕ × List (ℕ × ℕ × ℕ × ℕ))
  | "2.3.0.a.1" => some (2, [(1, 1, 0, 1)])
  | "2.6.0.a.1" => some (2, [(1, 0, 0, 1)])
  | "22.2.0.a.1" => some (22,
      [(1, 1, 21, 0), (1, 2, 0, 1), (1, 0, 2, 1), (21, 2, 20, 3), (13, 2, 13, 3)])
  | _ => none

end VerifiedLcalc
