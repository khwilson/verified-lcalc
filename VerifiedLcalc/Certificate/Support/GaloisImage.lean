/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes

import Mathlib.Tactic.FinCases
import TauCeti.NumberTheory.Padics.RingHoms

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

private theorem padicGL_map_surjective {p k : ℕ} [Fact p.Prime] [NeZero k] :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin 2)
      (PadicInt.toZModPow (p := p) k)) := by
  intro A
  let f := PadicInt.toZModPow (p := p) k
  choose entries hentries using fun (i j : Fin 2) =>
    ZMod.ringHom_surjective f ((A : Matrix (Fin 2) (Fin 2) _) i j)
  let M := Matrix.of entries
  have hM : M.map f = A.val := Matrix.ext hentries
  have hdet : IsUnit M.det := (isUnit_map_iff f _).mp (by
    rw [f.map_det, RingHom.mapMatrix_apply, hM]
    exact A.det.isUnit)
  exact ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext hM⟩

/-- The integral adelic reduction surjects onto the general linear group at every modulus. -/
theorem adelicReduction_surjective (N : ℕ+) : Function.Surjective (adelicReduction N) := by
  classical
  change Function.Surjective ((adelicCRT N).symm ∘ adelicPrimePowerReduction N)
  apply (adelicCRT N).symm.surjective.comp
  intro A
  have lifts (p : (N : ℕ).primeFactors) : ∃ g :
      Matrix.GeneralLinearGroup (Fin 2) (AdelicLocalRing
        ⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩),
      letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      Matrix.GeneralLinearGroup.map (PadicInt.toZModPow ((N : ℕ).factorization p.val)) g =
        A p := by
    letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    have hk := (Nat.prime_of_mem_primeFactors p.property).factorization_pos_of_dvd
      N.ne_zero (Nat.dvd_of_mem_primeFactors p.property)
    letI : NeZero ((N : ℕ).factorization p.val) := ⟨hk.ne'⟩
    exact padicGL_map_surjective (A p)
  choose lift hlift using lifts
  let g : AdelicGL := fun p =>
    if hp : p.val ∈ (N : ℕ).primeFactors then lift ⟨p.val, hp⟩ else 1
  refine ⟨g, ?_⟩
  funext p
  change Matrix.GeneralLinearGroup.map _ (g _) = A p
  rw [show g ⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩ = lift p from
    dif_pos p.property]
  exact hlift p

/-- The finite reduction at a level with full kernel containment has the original index. -/
theorem adelicReduction_index_eq {H : Subgroup AdelicGL} {N : ℕ+}
    (h : (adelicReduction N).ker ≤ H) : (H.map (adelicReduction N)).index = H.index :=
  H.index_map_eq (adelicReduction_surjective N) h

/-- A subgroup containing the reduction kernel is the full inverse image of its reduction. -/
theorem adelic_comap_map_eq {H : Subgroup AdelicGL} {N : ℕ+}
    (h : (adelicReduction N).ker ≤ H) :
    (H.map (adelicReduction N)).comap (adelicReduction N) = H :=
  Subgroup.comap_map_eq_self h

/-- The integral pullback at a certified level is cut out by the finite reduction of the image. -/
theorem adelicCongruenceSubgroup_eq_comap {H : Subgroup AdelicGL} {N : ℕ+}
    (h : (adelicReduction N).ker ≤ H) :
    adelicCongruenceSubgroup H = (H.map (adelicReduction N)).comap
      ((adelicReduction N).comp adelicSL2) := by
  rw [← Subgroup.comap_comap, adelic_comap_map_eq h, adelicCongruenceSubgroup]

/-- The genus recorded in the witness is the topological genus of the coarse modular curve. -/
theorem AdelicGenusFact.genus_eq {H : Subgroup AdelicGL} (fact : AdelicGenusFact H) :
    letI := fact.finiteCW
    TauCeti.RiemannSurface.genus (adelicProjectiveSubgroup H).CompactifiedQuotient =
      fact.genus := by
  letI := fact.finiteCW
  exact TauCeti.RiemannSurface.genus_eq_of_eulerChar_eq fact.correct

end VerifiedLcalc
