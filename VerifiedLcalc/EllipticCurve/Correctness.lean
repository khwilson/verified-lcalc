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

/-- The actual mathlib Weierstrass model specified by the input coefficients. -/
def weierstrass (e : CurveEquation) (R : Type*) [CommRing R] : WeierstrassCurve R :=
  ⟨e.a1, e.a2, e.a3, e.a4, e.a6⟩

theorem weierstrass_correct (e : CurveEquation) (R : Type*) [CommRing R] :
    (weierstrass e R).a₁ = (e.a1 : R) ∧ (weierstrass e R).a₂ = (e.a2 : R) ∧
    (weierstrass e R).a₃ = (e.a3 : R) ∧ (weierstrass e R).a₄ = (e.a4 : R) ∧
    (weierstrass e R).a₆ = (e.a6 : R) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Integer input equations commute with every coefficient-ring map. -/
theorem weierstrass_map (e : CurveEquation) {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : (weierstrass e R).map f = weierstrass e S := by
  ext <;> simp [weierstrass]

theorem weierstrass_discriminant (e : CurveEquation) (R : Type*) [CommRing R] :
    (weierstrass e R).Δ = (discriminant e : R) := by
  rw [← weierstrass_map e (Int.castRingHom R), WeierstrassCurve.map_Δ]
  rfl

theorem weierstrass_c4 (e : CurveEquation) (R : Type*) [CommRing R] :
    (weierstrass e R).c₄ = ((weierstrass e ℤ).c₄ : R) := by
  rw [← weierstrass_map e (Int.castRingHom R), WeierstrassCurve.map_c₄]
  rfl

theorem b2_correct (e : CurveEquation) : b2 e = (weierstrass e Int).b₂ := rfl
theorem b4_correct (e : CurveEquation) : b4 e = (weierstrass e Int).b₄ := rfl
theorem b6_correct (e : CurveEquation) : b6 e = (weierstrass e Int).b₆ := rfl
theorem b8_correct (e : CurveEquation) : b8 e = (weierstrass e Int).b₈ := rfl
theorem discriminant_correct (e : CurveEquation) :
    discriminant e = (weierstrass e Int).Δ := rfl

theorem residual_correct (e : CurveEquation) (x y : Int) (R : Type*) [CommRing R] :
    (residual e x y : R) =
      (y : R) ^ 2 + (weierstrass e R).a₁ * x * y + (weierstrass e R).a₃ * y -
        ((x : R) ^ 3 + (weierstrass e R).a₂ * (x : R) ^ 2 +
          (weierstrass e R).a₄ * x + (weierstrass e R).a₆) := by
  simp [residual, weierstrass]

/-- Boolean modular evaluation is exactly mathlib's affine equation. -/
theorem onCurve_equation (e : CurveEquation) (p : Nat) (xy : Fin p × Fin p) :
    onCurve e p xy = true ↔
      (weierstrass e (ZMod p)).toAffine.Equation (xy.1.val : ZMod p) (xy.2.val : ZMod p) := by
  rw [onCurve_correct, ← Int.dvd_iff_emod_eq_zero,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    WeierstrassCurve.Affine.equation_iff']
  simp only [residual_correct, Int.cast_natCast]

/-- Trial division is a proved primality test. -/
theorem isPrime_correct (p : Nat) : isPrime p = true ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, ne_eq, ← Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun d h2 hlt => ?_⟩
    rcases hd d hlt with h | h
    · omega
    · exact h
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun d hlt => ?_⟩
    by_cases h2 : d < 2
    · exact Or.inl h2
    · exact Or.inr (hd d (by omega) hlt)

/-- Modular discriminant testing really proves smooth reduction. -/
theorem goodReduction_correct (e : CurveEquation) (p : Nat) :
    goodReduction e p = true ↔ (weierstrass e (ZMod p)).Δ ≠ 0 := by
  simp only [goodReduction, decide_eq_true_eq, ne_eq, ← Int.dvd_iff_emod_eq_zero,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [discriminant, b2, b4, b6, b8, weierstrass, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The enumerator visits each modular solution exactly once. -/
theorem affinePoints_nodup (e : CurveEquation) (p : Nat) : (affinePoints e p).Nodup := by
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
def AffineSolutions (e : CurveEquation) (p : Nat) :=
  {xy : ZMod p × ZMod p // (weierstrass e (ZMod p)).toAffine.Equation xy.1 xy.2}

/-- Every residue has a unique representative in `Fin p`, for p nonzero. -/
def residueEquiv (p : Nat) [NeZero p] : Fin p ≃ ZMod p where
  toFun x := (x.val : ZMod p)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv x := by
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt]
  right_inv x := by simp

def solutionEquiv (e : CurveEquation) (p : Nat) [NeZero p] :
    {xy : Fin p × Fin p // onCurve e p xy = true} ≃ AffineSolutions e p :=
  ((residueEquiv p).prodCongr (residueEquiv p)).subtypeEquiv
    (fun xy => onCurve_equation e p xy)

theorem affineCount_correct (e : CurveEquation) (p : Nat) [NeZero p] :
    affineCount e p = Nat.card (AffineSolutions e p) := by
  classical
  let s : Finset (Fin p × Fin p) := Finset.univ.filter (fun xy => onCurve e p xy = true)
  have hs : (affinePoints e p).toFinset = s := by
    ext xy
    simp [s, affinePoints_correct]
  rw [affineCount, ← List.toFinset_card_of_nodup (affinePoints_nodup e p), hs]
  rw [← Nat.card_congr (solutionEquiv e p)]
  simp [s, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem pointCount_correct (e : CurveEquation) (p : Nat) [NeZero p] :
    pointCount e p = Nat.card (AffineSolutions e p) + 1 := by
  rw [pointCount, affineCount_correct]

theorem frobeniusTrace_correct (e : CurveEquation) (p : Nat) [NeZero p] :
    frobeniusTrace e p = (p : Int) + 1 - (Nat.card (AffineSolutions e p) + 1 : Nat) := by
  rw [frobeniusTrace, pointCount_correct]

/-- At good reduction the projective equation count is the cardinality of the
actual mathlib elliptic-curve point type, including its point at infinity. -/
theorem pointCount_eq_card_point (e : CurveEquation) (p : Nat) [NeZero p]
    [Nontrivial (ZMod p)]
    [(weierstrass e (ZMod p)).IsElliptic] :
    pointCount e p = Nat.card (weierstrass e (ZMod p)).toAffine.Point := by
  let : Finite (AffineSolutions e p) := by unfold AffineSolutions; infer_instance
  rw [pointCount_correct, Nat.card_congr (weierstrass e (ZMod p)).toAffine.pointEquiv]
  exact Finite.card_option.symm

/-- End-to-end arithmetic guarantee for every supported prime calculation. -/
theorem analysePrime_sound (e : CurveEquation) (p : Nat) (d : PrimeData)
    (h : analysePrime e p = some d) :
    Nat.Prime p ∧ d.prime = p ∧
      d.points = Nat.card (weierstrass e (ZMod p)).toAffine.Point ∧
      d.trace = (p : Int) + 1 - Nat.card (weierstrass e (ZMod p)).toAffine.Point := by
  obtain ⟨hp, hg, hd, hpoints, htrace⟩ := analysePrime_correct e p d h
  have hp' := (isPrime_correct p).mp hp
  let : Fact (Nat.Prime p) := ⟨hp'⟩
  let : NeZero p := ⟨hp'.ne_zero⟩
  have hΔ := (goodReduction_correct e p).mp hg
  let : (weierstrass e (ZMod p)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  refine ⟨hp', hd, hpoints.trans (pointCount_eq_card_point e p), ?_⟩
  rw [htrace, frobeniusTrace, pointCount_eq_card_point]

end VerifiedLcalc.EllipticCurve
