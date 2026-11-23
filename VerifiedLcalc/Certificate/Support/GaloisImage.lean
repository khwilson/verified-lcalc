/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes

/-! # Matrix encoding for the finite image reported in an adelic Galois row -/

@[expose] public section

namespace VerifiedLcalc

/-- Encode the generators as LMFDB row-major quadruples, using least nonnegative residues. -/
def FiniteGaloisImageFact.matrixRows {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)]
    (fact : FiniteGaloisImageFact curve) :
    List (ℕ × ℕ × ℕ × ℕ) :=
  fact.generators.map fun g =>
    let m := (g : Matrix (Fin 2) (Fin 2) (ZMod (fact.modulus : ℕ)))
    ((m 0 0).val, (m 0 1).val, (m 1 0).val, (m 1 1).val)

end VerifiedLcalc
