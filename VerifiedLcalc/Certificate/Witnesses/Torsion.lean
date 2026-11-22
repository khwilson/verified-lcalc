/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Torsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount

/-! # Rational torsion certificate data -/

@[expose] public section

namespace VerifiedLcalc

/-- Two proposed odd primes and the gcd of the corresponding finite-field point counts. -/
structure TorsionBoundWitness where
  /-- First proposed prime of good reduction. -/
  firstPrime : Nat
  /-- Second proposed prime of good reduction. -/
  secondPrime : Nat
  /-- Claimed positive gcd of the two reduced point counts. -/
  bound : Nat

/-- A positive common point-count divisor bounding the full rational torsion subgroup. -/
structure TorsionDivisorFacts (curve : WeierstrassCurve ℤ) where
  /-- The submitted primes and proposed gcd. -/
  evidence : TorsionBoundWitness
  /-- The first prime is prime and odd. -/
  firstPrime_prime : evidence.firstPrime.Prime
  firstPrime_odd : evidence.firstPrime ≠ 2
  /-- The first finite-field equation is nonsingular. -/
  firstGoodReduction :
    letI : Fact evidence.firstPrime.Prime := ⟨firstPrime_prime⟩
    (curve.baseChange (ZMod evidence.firstPrime)).IsElliptic
  /-- The second prime is prime and odd. -/
  secondPrime_prime : evidence.secondPrime.Prime
  secondPrime_odd : evidence.secondPrime ≠ 2
  /-- The second finite-field equation is nonsingular. -/
  secondGoodReduction :
    letI : Fact evidence.secondPrime.Prime := ⟨secondPrime_prime⟩
    (curve.baseChange (ZMod evidence.secondPrime)).IsElliptic
  /-- The claimed value is exactly the gcd of TauCeti's mathematical point counts. -/
  pointCountGcd :
    letI : Fact evidence.firstPrime.Prime := ⟨firstPrime_prime⟩
    letI : Fact evidence.secondPrime.Prime := ⟨secondPrime_prime⟩
    Nat.gcd (curve.baseChange (ZMod evidence.firstPrime)).pointCount
      (curve.baseChange (ZMod evidence.secondPrime)).pointCount = evidence.bound
  /-- The full rational torsion cardinality divides the positive bound. -/
  valid : Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) ∣
    evidence.bound ∧ 0 < evidence.bound
  /-- A supplied exact count consistent with the bound. -/
  consistentClaim : Option { n : ℕ // 0 < n ∧ n ∣ evidence.bound } := none

/-- Checked invariant factors and a generator-preserving equivalence for cyclic torsion. -/
structure CyclicTorsionFacts (curve : WeierstrassCurve ℤ) where
  /-- The supplied invariant factors. -/
  factors : List ℕ
  /-- The order of the whole cyclic group. -/
  order : ℕ
  /-- The selected rational point, or the identity for trivial torsion. -/
  generator : (curve.baseChange ℚ).toAffine.Point
  /-- The canonical factors and an equivalence sending one to the selected point. -/
  structure_eq : factors = (if order = 1 then [] else [order]) ∧
    ∃ e : ZMod order ≃+ AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point,
      (e 1 : (curve.baseChange ℚ).toAffine.Point) = generator

/-- A checked two-factor presentation of the full rational torsion subgroup. -/
structure TwoFactorTorsionFacts (curve : WeierstrassCurve ℤ) where
  /-- The order of the second supplied generator; the first factor has order two. -/
  secondOrder : ℕ
  /-- The second generator has positive exact order, so this is not a sentinel case. -/
  secondOrder_pos : 0 < secondOrder
  /-- The second invariant factor is divisible by the first factor. -/
  first_factor_dvd_second : 2 ∣ secondOrder
  /-- The order-two rational point in the supplied invariant-factor ordering. -/
  firstGenerator : (curve.baseChange ℚ).toAffine.Point
  /-- The rational point whose order is `secondOrder`. -/
  secondGenerator : (curve.baseChange ℚ).toAffine.Point
  /-- The actual additive equivalence onto Mathlib's full torsion subgroup. -/
  equivalence : ZMod 2 × ZMod secondOrder ≃+
    AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point
  /-- The first coordinate generator maps to `firstGenerator`. -/
  maps_first : (equivalence (1, 0) : (curve.baseChange ℚ).toAffine.Point) = firstGenerator
  /-- The second coordinate generator maps to `secondGenerator`. -/
  maps_second : (equivalence (0, 1) : (curve.baseChange ℚ).toAffine.Point) = secondGenerator
  /-- The equivalence certifies the full subgroup cardinality. -/
  cardinality : Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) =
    2 * secondOrder

/-- Exact distinct prime support of a finite rational torsion subgroup. -/
structure TorsionPrimeSupportFacts (curve : WeierstrassCurve ℤ) where
  /-- The distinct prime divisors of the exact group order. -/
  primes : List ℕ
  /-- Each prime appears at most once. -/
  nodup : primes.Nodup
  /-- The list contains exactly the prime divisors of the full subgroup order. -/
  exact_support : ∀ p, p ∈ primes ↔ p.Prime ∧
    p ∣ Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point)

/-- Partial divisibility bounds and exact cardinality assertions for the torsion subgroup. -/
structure TorsionFacts (curve : WeierstrassCurve ℤ) where
  /-- Evidence that the full torsion order divides a checked positive bound. -/
  divisor : Option (TorsionDivisorFacts curve) := none
  /-- The exact cardinality of the whole torsion subgroup when determined. -/
  cardinality : Option { n : ℕ //
    Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n } := none
  /-- The checked cyclic structure, if requested and determined. -/
  cyclicStructure : Option (CyclicTorsionFacts curve) := none
  /-- The checked `[2, n]` structure and generator-preserving equivalence, if determined. -/
  twoFactorStructure : Option (TwoFactorTorsionFacts curve) := none
  /-- Exact distinct prime support, only when the full torsion cardinality is known. -/
  primeSupport : Option (TorsionPrimeSupportFacts curve) := none

end VerifiedLcalc
