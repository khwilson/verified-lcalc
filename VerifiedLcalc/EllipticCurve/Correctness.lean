module

public import VerifiedLcalc.EllipticCurve.Arithmetic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace VerifiedLcalc.EllipticCurve
open Artifacts

theorem weierstrass_correct (e : (WeierstrassCurve ℤ)) (R : Type*) [CommRing R] :
    (WeierstrassCurve.baseChange e R).a₁ = (e.a₁ : R) ∧ (WeierstrassCurve.baseChange e R).a₂ = (e.a₂ : R) ∧
    (WeierstrassCurve.baseChange e R).a₃ = (e.a₃ : R) ∧ (WeierstrassCurve.baseChange e R).a₄ = (e.a₄ : R) ∧
    (WeierstrassCurve.baseChange e R).a₆ = (e.a₆ : R) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Integer input equations commute with every coefficient-ring map. -/
theorem weierstrass_map (e : (WeierstrassCurve ℤ)) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : (WeierstrassCurve.baseChange e R).map f = WeierstrassCurve.baseChange e S := by
  ext <;> simp [WeierstrassCurve.baseChange]

theorem weierstrass_discriminant (e : (WeierstrassCurve ℤ)) (R : Type*) [CommRing R] :
    (WeierstrassCurve.baseChange e R).Δ = (e.Δ : R) := by
  rw [← weierstrass_map e (Int.castRingHom R), WeierstrassCurve.map_Δ]
  rfl

theorem weierstrass_c4 (e : (WeierstrassCurve ℤ)) (R : Type*) [CommRing R] :
    (WeierstrassCurve.baseChange e R).c₄ = (e.c₄ : R) := by
  rw [← weierstrass_map e (Int.castRingHom R), WeierstrassCurve.map_c₄]
  rfl

theorem residual_correct (e : (WeierstrassCurve ℤ)) (x y : Int) (R : Type*) [CommRing R] :
    (residual e x y : R) =
      (y : R) ^ 2 + (WeierstrassCurve.baseChange e R).a₁ * x * y + (WeierstrassCurve.baseChange e R).a₃ * y -
        ((x : R) ^ 3 + (WeierstrassCurve.baseChange e R).a₂ * (x : R) ^ 2 +
          (WeierstrassCurve.baseChange e R).a₄ * x + (WeierstrassCurve.baseChange e R).a₆) := by
  simp [residual, WeierstrassCurve.baseChange]

/-- Boolean modular evaluation is exactly mathlib's affine equation. -/
theorem onCurve_equation (e : (WeierstrassCurve ℤ)) (p : Nat) (xy : Fin p × Fin p) :
    onCurve e p xy = true ↔
      (WeierstrassCurve.baseChange e (ZMod p)).toAffine.Equation (xy.1.val : ZMod p) (xy.2.val : ZMod p) := by
  rw [onCurve_correct, ← Int.dvd_iff_emod_eq_zero,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    WeierstrassCurve.Affine.equation_iff']
  simp only [residual_correct, Int.cast_natCast]

/-- The backend uses Mathlib's primality decision procedure directly. -/
theorem isPrime_correct (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  simp [isPrime]

/-- Modular discriminant testing really proves smooth reduction. -/
theorem goodReduction_correct (e : (WeierstrassCurve ℤ)) (p : Nat) :
    goodReduction e p = true ↔ (WeierstrassCurve.baseChange e (ZMod p)).Δ ≠ 0 := by
  simp only [goodReduction, decide_eq_true_eq, ne_eq, ← Int.dvd_iff_emod_eq_zero,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [WeierstrassCurve.baseChange, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The enumerator visits each modular solution exactly once. -/
theorem affinePoints_nodup (e : (WeierstrassCurve ℤ)) (p : Nat) : (affinePoints e p).Nodup := by
  unfold affinePoints
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  constructor
  · intro x hx
    exact (List.nodup_finRange p).map (by intro y z h; exact (Prod.mk.inj h).2)
  · apply (List.nodup_finRange p).imp
    intro x y hxy
    simp only [List.disjoint_left, List.mem_map]
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    exact hxy (Prod.mk.inj he).1.symm

/-- The finite field solution type, including singular solutions. This agrees
with TauCeti's projective-model point-count convention after adjoining infinity. -/
def AffineSolutions (e : (WeierstrassCurve ℤ)) (p : Nat) :=
  {xy : ZMod p × ZMod p // (WeierstrassCurve.baseChange e (ZMod p)).toAffine.Equation xy.1 xy.2}

/-- Every residue has a unique representative in `Fin p`, for p nonzero. -/
def residueEquiv (p : Nat) [NeZero p] : Fin p ≃ ZMod p where
  toFun x := (x.val : ZMod p)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv x := by
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
  right_inv x := by simp

def solutionEquiv (e : (WeierstrassCurve ℤ)) (p : Nat) [NeZero p] :
    {xy : Fin p × Fin p // onCurve e p xy = true} ≃ AffineSolutions e p :=
  ((residueEquiv p).prodCongr (residueEquiv p)).subtypeEquiv
    (fun xy => onCurve_equation e p xy)

theorem affineCount_correct (e : (WeierstrassCurve ℤ)) (p : Nat) [NeZero p] :
    affineCount e p = Nat.card (AffineSolutions e p) := by
  classical
  let s : Finset (Fin p × Fin p) := Finset.univ.filter (fun xy => onCurve e p xy = true)
  have hs : (affinePoints e p).toFinset = s := by
    ext xy
    simp [s, affinePoints_correct]
  rw [affineCount, ← List.toFinset_card_of_nodup (affinePoints_nodup e p), hs]
  rw [← Nat.card_congr (solutionEquiv e p)]
  simp [s, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem computePointCount_correct (e : (WeierstrassCurve ℤ)) (p : Nat) [NeZero p] :
    computePointCount e p = Nat.card (AffineSolutions e p) + 1 := by
  rw [computePointCount, affineCount_correct]

theorem frobeniusTrace_correct (e : (WeierstrassCurve ℤ)) (p : Nat) [NeZero p] :
    frobeniusTrace e p = (p : Int) + 1 - (Nat.card (AffineSolutions e p) + 1 : Nat) := by
  rw [frobeniusTrace, computePointCount_correct]

/-- At good reduction the projective equation count is the cardinality of the
actual mathlib elliptic-curve point type, including its point at infinity. -/
theorem computePointCount_eq_card_point (e : (WeierstrassCurve ℤ)) (p : Nat) [NeZero p]
    [Nontrivial (ZMod p)]
    [(WeierstrassCurve.baseChange e (ZMod p)).IsElliptic] :
    computePointCount e p = Nat.card (WeierstrassCurve.baseChange e (ZMod p)).toAffine.Point := by
  let : Finite (AffineSolutions e p) := by unfold AffineSolutions; infer_instance
  rw [computePointCount_correct, Nat.card_congr (WeierstrassCurve.baseChange e (ZMod p)).toAffine.pointEquiv]
  exact Finite.card_option.symm

/-- End-to-end arithmetic guarantee for every supported prime calculation. -/
theorem analysePrime_sound (e : (WeierstrassCurve ℤ)) (p : Nat) (d : PrimeData)
    (h : analysePrime e p = some d) :
    Nat.Prime p ∧ d.prime = p ∧
      d.points = Nat.card (WeierstrassCurve.baseChange e (ZMod p)).toAffine.Point ∧
      d.trace = (p : Int) + 1 - Nat.card (WeierstrassCurve.baseChange e (ZMod p)).toAffine.Point := by
  obtain ⟨hp, hg, hd, hpoints, htrace⟩ := analysePrime_correct e p d h
  have hp' := (isPrime_correct p).mp hp
  let : Fact (Nat.Prime p) := ⟨hp'⟩
  let : NeZero p := ⟨hp'.ne_zero⟩
  have hΔ := (goodReduction_correct e p).mp hg
  let : (WeierstrassCurve.baseChange e (ZMod p)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  refine ⟨hp', hd, hpoints.trans (computePointCount_eq_card_point e p), ?_⟩
  rw [htrace, frobeniusTrace, computePointCount_eq_card_point]

end VerifiedLcalc.EllipticCurve
