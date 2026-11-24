/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.EllipticCurve.Modularity.RealizationData
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.RealPeriod
public import TauCeti.NumberTheory.ModularForms.GeodesicIntegral.BetweenCusps
public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscreteValuationRing
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.LinearCombination

/-! # Ordinary and signed cyclotomic interpolation of elliptic modular symbols

For the trivial tame character at an odd prime, use the cyclotomic generator
`1 + p`. The finite coefficients are sums over the Teichmüller representatives.
Congruences are in the integral power-series ring, so passage to the fraction
field cannot erase the nonconstant character data.
-/

@[expose] public noncomputable section

namespace VerifiedLcalc.Modularity

open PowerSeries OnePoint
open scoped BigOperators

/-- The real modular symbol of a weight-two realization, normalized by the curve's
full minimal real period. The orientation is from the cusp at infinity to the rational cusp. -/
def normalizedRealModularSymbol {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (realization : ModularRealization curve) (r : ℚ) : ℝ :=
  (2 * Real.pi * Complex.I * TauCeti.cuspIntegral realization.form ∞ (r : OnePoint ℚ)).re /
    (curve.baseChange ℚ).minimalRealPeriod

variable {p : ℕ} [Fact p.Prime]

/-- The exponent representative of `(1+p)^j [a]` modulo `p^(n+1)`.
Raising a lift of `a` to `p^n` projects to the Teichmüller factor. -/
def mazurTateResidue (p n j a : ℕ) : ℕ :=
  ((1 + p) ^ j * a ^ (p ^ n)) % (p ^ (n + 1))

/-- The finite Mazur–Tate element at cyclotomic level `n`, for the trivial tame character. -/
def mazurTateSeries (symbol : ℚ → ℤ_[p]) (n : ℕ) : PowerSeries ℤ_[p] :=
  ∑ j ∈ Finset.range (p ^ n), C (∑ a ∈ Finset.Ico 1 p,
    symbol ((mazurTateResidue p n j a : ℚ) / (p : ℚ) ^ (n + 1))) * (1 + X) ^ j

/-- `(1+T)^(p^n) - 1`, defining the finite cyclotomic quotient. -/
def cyclotomicModulus (n : ℕ) : PowerSeries ℤ_[p] := (1 + X) ^ (p ^ n) - 1

/-- Trace from the preceding level. At level zero the projection from the trivial
character of the full unit group has fibre of size `p-1`. -/
def cyclotomicTransfer (n : ℕ) : PowerSeries ℤ_[p] :=
  match n with
  | 0 => C (p - 1 : ℤ_[p])
  | m + 1 => ∑ i ∈ Finset.range p, (1 + X) ^ (i * p ^ m)

/-- The preceding Mazur–Tate element, with the symbol at zero at level minus one. -/
def priorMazurTate (symbol : ℚ → ℤ_[p]) (n : ℕ) : PowerSeries ℤ_[p] :=
  match n with
  | 0 => C (symbol 0)
  | m + 1 => mazurTateSeries symbol m

/-- The normalized `p`-stabilized finite-level element at a good ordinary prime. -/
def ordinaryMazurTate (symbol : ℚ → ℤ_[p]) (alpha : ℤ_[p]ˣ) (n : ℕ) :
    PowerSeries ℤ_[p] :=
  C (↑(alpha⁻¹ ^ (n + 1)) : ℤ_[p]) *
    (mazurTateSeries symbol n - C (↑alpha⁻¹ : ℤ_[p]) *
      cyclotomicTransfer n * priorMazurTate symbol n)

/-- Compatibility at every finite level with the normalized ordinary distribution. -/
def OrdinarilyInterpolates (symbol : ℚ → ℤ_[p]) (alpha : ℤ_[p]ˣ)
    (series : PowerSeries ℤ_[p]) : Prop :=
  ∀ n, cyclotomicModulus n ∣ series - ordinaryMazurTate symbol alpha n

/-- At a multiplicative prime the form is already stabilized and no transfer is subtracted. -/
def MultiplicativelyInterpolates (symbol : ℚ → ℤ_[p]) (alpha : ℤ_[p]ˣ)
    (series : PowerSeries ℤ_[p]) : Prop :=
  ∀ n, cyclotomicModulus n ∣
    series - C (↑(alpha⁻¹ ^ (n + 1)) : ℤ_[p]) * mazurTateSeries symbol n

/-- Product of the cyclotomic trace factors of parity opposite to the level,
as in Pollack's finite-level signed interpolation for `aₚ = 0`. -/
def signedFactor (n : ℕ) : PowerSeries ℤ_[p] :=
  ∏ m ∈ (Finset.range n).filter (fun m => (m + 1) % 2 ≠ n % 2),
    cyclotomicTransfer (m + 1)

/-- Compatibility at every finite level, with the minus series at even levels
and the plus series at odd levels in the odd-prime convention. -/
def SignedlyInterpolates (symbol : ℚ → ℤ_[p])
    (plus minus : PowerSeries ℤ_[p]) : Prop :=
  ∀ n, cyclotomicModulus n ∣
    mazurTateSeries symbol n - C ((-1 : ℤ_[p]) ^ (n / 2)) * signedFactor n *
      (if n % 2 = 0 then minus else plus)

/-- On the submitted globally minimal model, good reduction is detected by the discriminant. -/
def iwasawaGood (curve : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  (curve.baseChange (ZMod p)).Δ ≠ 0

/-- The arithmetic Euler coefficient determining the local Euler factor. -/
def iwasawaTrace (curve : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (curve.baseChange ℚ).LFunction p

/-- The reciprocal ordinary root of the local good Euler factor. -/
def IsOrdinaryRoot (curve : WeierstrassCurve ℤ) (alpha : ℤ_[p]ˣ) : Prop :=
  (alpha : ℤ_[p]) ^ 2 - (iwasawaTrace curve p : ℤ_[p]) * alpha + p = 0

/-- A good ordinary or multiplicative row uses the corresponding normalized unsigned series. -/
def UnsignedIwasawaInterpolation (curve : WeierstrassCurve ℤ) (symbol : ℚ → ℤ_[p])
    (alpha : ℤ_[p]ˣ) (series : PowerSeries ℤ_[p]) : Prop :=
  (iwasawaGood curve p ∧ IsOrdinaryRoot curve alpha ∧ OrdinarilyInterpolates symbol alpha series) ∨
  (¬ iwasawaGood curve p ∧ (curve.baseChange (ZMod p)).c₄ ≠ 0 ∧
    (alpha : ℤ_[p]) = (iwasawaTrace curve p : ℤ_[p]) ∧
    MultiplicativelyInterpolates symbol alpha series)

/-- Cyclotomic congruences preserve the constant coefficient. -/
theorem constantCoeff_eq_of_cyclotomicModulus_dvd {n : ℕ} {F G : PowerSeries ℤ_[p]}
    (h : cyclotomicModulus n ∣ F - G) :
    constantCoeff F = constantCoeff G := by
  obtain ⟨Q, hQ⟩ := h
  have eq := congrArg (constantCoeff (R := ℤ_[p])) hQ
  simpa [cyclotomicModulus, sub_eq_zero] using eq

/-- At a good ordinary prime the level-zero distribution yields the usual Euler
factor squared times the period-normalized symbol at zero. -/
theorem OrdinarilyInterpolates.constantCoeff_eq {curve : WeierstrassCurve ℤ}
    {symbol : ℚ → ℤ_[p]} {alpha : ℤ_[p]ˣ} {series : PowerSeries ℤ_[p]}
    (h : OrdinarilyInterpolates symbol alpha series) (root : IsOrdinaryRoot curve alpha)
    (sum : constantCoeff (mazurTateSeries symbol 0) =
      ((iwasawaTrace curve p : ℤ_[p]) - 2) * symbol 0) :
    constantCoeff series = (1 - (↑alpha⁻¹ : ℤ_[p])) ^ 2 * symbol 0 := by
  have ha : (alpha : ℤ_[p]) * (↑alpha⁻¹ : ℤ_[p]) = 1 := Units.mul_inv alpha
  have hsum : (iwasawaTrace curve p : ℤ_[p]) =
      (alpha : ℤ_[p]) + (p : ℤ_[p]) * (↑alpha⁻¹ : ℤ_[p]) := by
    have hroot : (iwasawaTrace curve p : ℤ_[p]) * (alpha : ℤ_[p]) =
        (alpha : ℤ_[p]) ^ 2 + p := by
      unfold IsOrdinaryRoot at root
      linear_combination -root
    calc
      (iwasawaTrace curve p : ℤ_[p]) =
          ((iwasawaTrace curve p : ℤ_[p]) * (alpha : ℤ_[p])) * (↑alpha⁻¹ : ℤ_[p]) := by
        rw [mul_assoc, ha, mul_one]
      _ = (alpha : ℤ_[p]) + (p : ℤ_[p]) * (↑alpha⁻¹ : ℤ_[p]) := by
        rw [hroot, add_mul, pow_two, mul_assoc (alpha : ℤ_[p]), ha, mul_one]
  rw [constantCoeff_eq_of_cyclotomicModulus_dvd (h 0)]
  simp only [ordinaryMazurTate, cyclotomicTransfer, priorMazurTate, map_mul, map_sub,
    constantCoeff_C, Nat.zero_add, pow_one, sum, hsum]
  linear_combination (symbol 0) * ha

/-- The initial even and odd levels give the constant coefficients of the two signed series. -/
theorem SignedlyInterpolates.constantCoeff_eq {symbol : ℚ → ℤ_[p]}
    {plus minus : PowerSeries ℤ_[p]} (h : SignedlyInterpolates symbol plus minus) :
    constantCoeff minus = constantCoeff (mazurTateSeries symbol 0) ∧
      constantCoeff plus = constantCoeff (mazurTateSeries symbol 1) := by
  refine ⟨?_, ?_⟩
  · simpa [signedFactor] using (constantCoeff_eq_of_cyclotomicModulus_dvd (h 0)).symm
  · simpa [signedFactor, Finset.filter_singleton] using
      (constantCoeff_eq_of_cyclotomicModulus_dvd (h 1)).symm

/-- A unit constant coefficient forces both Weierstrass invariants to vanish. -/
theorem iwasawa_zero_of_constantCoeff_unit {F : PowerSeries ℤ_[p]}
    (h : IsUnit F.constantCoeff) : F.lambdaInvariant = 0 ∧ F.muInvariant = 0 :=
  let hF := isUnit_iff_constantCoeff.mpr h
  ⟨lambdaInvariant_eq_zero_of_isUnit hF, muInvariant_eq_zero_of_isUnit hF⟩

/-- A p-adic integer is a unit exactly when its reduction modulo the prime is nonzero. -/
theorem iwasawaIsUnit_iff_toZMod_ne_zero {a : ℤ_[p]} : IsUnit a ↔ PadicInt.toZMod a ≠ 0 := by
  rw [← not_iff_not, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, not_ne_iff]

/-- The nonanomalous condition on the actual arithmetic coefficient makes
the ordinary augmentation factor a unit. -/
theorem IsOrdinaryRoot.isUnit_one_sub_inv {curve : WeierstrassCurve ℤ}
    {alpha : ℤ_[p]ˣ} (root : IsOrdinaryRoot curve alpha)
    (htrace : (iwasawaTrace curve p : ZMod p) ≠ 1) :
    IsUnit (1 - (↑alpha⁻¹ : ℤ_[p])) := by
  apply iwasawaIsUnit_iff_toZMod_ne_zero.mpr
  intro hzero
  have hi : PadicInt.toZMod (↑alpha⁻¹ : ℤ_[p]) = 1 := by
    simpa using (sub_eq_zero.mp (by simpa using hzero : 1 -
      PadicInt.toZMod (↑alpha⁻¹ : ℤ_[p]) = 0)).symm
  have hu : PadicInt.toZMod (alpha : ℤ_[p]) *
        PadicInt.toZMod (↑alpha⁻¹ : ℤ_[p]) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ha : PadicInt.toZMod (alpha : ℤ_[p]) = 1 := by
    rwa [hi, mul_one] at hu
  apply htrace
  have hr := congrArg (PadicInt.toZMod (p := p)) root
  exact (sub_eq_zero.mp (by
    simpa [ha] using hr : 1 - (iwasawaTrace curve p : ZMod p) = 0)).symm

/-- The level-zero Hecke identity before ordinary stabilization. -/
def IwasawaLevelZeroIdentity (curve : WeierstrassCurve ℤ) (symbol : ℚ → ℤ_[p]) : Prop :=
  constantCoeff (mazurTateSeries symbol 0) =
    ((iwasawaTrace curve p : ℤ_[p]) - 2) * symbol 0

/-- The first two Hecke identities in the supersingular case with trace zero. -/
def IwasawaSignedInitialIdentities (symbol : ℚ → ℤ_[p]) : Prop :=
  constantCoeff (mazurTateSeries symbol 0) = -2 * symbol 0 ∧
    constantCoeff (mazurTateSeries symbol 1) = -((p : ℤ_[p]) - 1) * symbol 0

/-- The local interpolation and Hecke identities entering the good-prime unit criterion. -/
def GoodPrimeIwasawaInterpolation (curve : WeierstrassCurve ℤ) (symbol : ℚ → ℤ_[p]) : Prop :=
  (∃ alpha F, IsOrdinaryRoot curve alpha ∧ OrdinarilyInterpolates symbol alpha F ∧
    IwasawaLevelZeroIdentity curve symbol ∧ (iwasawaTrace curve p : ZMod p) ≠ 1) ∨
  (iwasawaTrace curve p = 0 ∧ IwasawaSignedInitialIdentities symbol ∧
    ∃ plus minus, SignedlyInterpolates symbol plus minus)

/-- Independent interpolation and arithmetic inputs for the good-prime unit criterion. -/
def GoodPrimeIwasawaUnitInput (curve : WeierstrassCurve ℤ) (symbol : ℚ → ℤ_[p]) : Prop :=
  IsUnit (symbol 0) ∧ GoodPrimeIwasawaInterpolation curve symbol

/-- There is an interpolant of the applicable good-prime type, and every interpolant
with the same normalized symbols has vanishing Iwasawa invariants. -/
def GoodPrimeIwasawaVanishing (curve : WeierstrassCurve ℤ) (symbol : ℚ → ℤ_[p]) : Prop :=
  ((∃ alpha F, IsOrdinaryRoot curve alpha ∧ OrdinarilyInterpolates symbol alpha F) ∧
    ∀ alpha F, IsOrdinaryRoot curve alpha → OrdinarilyInterpolates symbol alpha F →
      F.lambdaInvariant = 0 ∧ F.muInvariant = 0) ∨
  (iwasawaTrace curve p = 0 ∧
    (∃ plus minus, SignedlyInterpolates symbol plus minus) ∧
    ∀ plus minus, SignedlyInterpolates symbol plus minus →
      plus.lambdaInvariant = 0 ∧ plus.muInvariant = 0 ∧
      minus.lambdaInvariant = 0 ∧ minus.muInvariant = 0)

/-- The unit criterion for the ordinary series follows from the level-zero Hecke identity. -/
theorem OrdinarilyInterpolates.unit_of_augmentation {curve : WeierstrassCurve ℤ}
    {symbol : ℚ → ℤ_[p]} {alpha : ℤ_[p]ˣ} {series : PowerSeries ℤ_[p]}
    (interp : OrdinarilyInterpolates symbol alpha series) (root : IsOrdinaryRoot curve alpha)
    (sum : IwasawaLevelZeroIdentity curve symbol)
    (trace_ne_one : (iwasawaTrace curve p : ZMod p) ≠ 1) (symbol_unit : IsUnit (symbol 0)) :
    IsUnit series.constantCoeff := by
  rw [interp.constantCoeff_eq root sum]
  exact ((root.isUnit_one_sub_inv trace_ne_one).pow 2).mul symbol_unit

/-- Good-prime vanishing follows from the actual normalized interpolation and unit conditions. -/
theorem GoodPrimeIwasawaUnitInput.vanishing {curve : WeierstrassCurve ℤ}
    {symbol : ℚ → ℤ_[p]} (hp : 5 ≤ p) (h : GoodPrimeIwasawaUnitInput curve symbol) :
    GoodPrimeIwasawaVanishing curve symbol := by
  obtain ⟨hunit, hord | hss⟩ := h
  · obtain ⟨alpha, F, hroot, hinterp, hsum, htrace⟩ := hord
    refine Or.inl ⟨⟨alpha, F, hroot, hinterp⟩, fun _ _ root interp ↦ ?_⟩
    exact iwasawa_zero_of_constantCoeff_unit (interp.unit_of_augmentation root hsum htrace hunit)
  · obtain ⟨htrace, ⟨hzero, hone⟩, exists_pair⟩ := hss
    refine Or.inr ⟨htrace, exists_pair, fun plus minus hinterp ↦ ?_⟩
    have ht : (2 : ZMod p) ≠ 0 := by
      exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
        (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    have htwo : IsUnit (2 : ℤ_[p]) := iwasawaIsUnit_iff_toZMod_ne_zero.mpr (by
      change PadicInt.toZMod ((2 : ℕ) : ℤ_[p]) ≠ 0
      rw [map_natCast]
      exact ht)
    have hpred : IsUnit ((p : ℤ_[p]) - 1) :=
      iwasawaIsUnit_iff_toZMod_ne_zero.mpr (by simp)
    obtain ⟨hm, hp'⟩ := hinterp.constantCoeff_eq
    have hM : IsUnit minus.constantCoeff := by
      rw [hm, hzero]
      exact htwo.neg.mul hunit
    have hP : IsUnit plus.constantCoeff := by
      rw [hp', hone]
      exact hpred.neg.mul hunit
    exact ⟨(iwasawa_zero_of_constantCoeff_unit hP).1, (iwasawa_zero_of_constantCoeff_unit hP).2,
      iwasawa_zero_of_constantCoeff_unit hM⟩

end VerifiedLcalc.Modularity
