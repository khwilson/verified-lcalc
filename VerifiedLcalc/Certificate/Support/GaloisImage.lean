/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes

import Mathlib.Tactic.FinCases

/-! # Matrix encoding and residual Galois image facts -/

@[expose] public section

namespace VerifiedLcalc

/-- At a nonzero modulus the four reduced entries determine the matrix. -/
theorem galoisMatrixRow_injective {p : ℕ} [NeZero p] :
    Function.Injective (galoisMatrixRow (p := p)) := by
  intro g h eqRows
  apply Units.ext
  ext i j
  apply ZMod.val_injective p
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst eqRows
  · exact congrArg (fun row => row.2.1) eqRows
  · exact congrArg (fun row => row.2.2.1) eqRows
  · exact congrArg (fun row => row.2.2.2) eqRows

/-- Encode the generators as LMFDB row-major quadruples, using least nonnegative residues. -/
def FiniteGaloisImageFact.matrixRows {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)]
    (fact : FiniteGaloisImageFact curve) :
    List (ℕ × ℕ × ℕ × ℕ) :=
  fact.generators.map galoisMatrixRow

/-- Every source label in a checked list has exact residual evidence on the same curve. -/
theorem ModPrimeImageListFact.exists_of_mem_labels {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] [DecidableEq (AlgebraicClosure ℚ)]
    (fact : ModPrimeImageListFact curve) {label : String}
    (h : label ∈ fact.images.map ModPrimeImageFact.label) :
    ∃ entry ∈ fact.images, entry.label = label :=
  List.mem_map.mp h

end VerifiedLcalc
