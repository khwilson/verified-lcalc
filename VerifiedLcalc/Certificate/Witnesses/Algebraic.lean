/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import VerifiedLcalc.Certificate.PointAccessors
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.GroupTheory.Torsion

/-! # Rational and integral points, Mordell–Weil invariants and isogenies -/

@[expose] public section

/-! ## Mordell–Weil rank and regulator -/

namespace VerifiedLcalc.EllipticCurve

/-- Checked lower and upper bounds on the Mordell–Weil rank of a nonsingular
rational Weierstrass curve. -/
structure AlgebraicRankBounds (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic] where
  /-- The claimed lower endpoint. -/
  lower : ℕ
  /-- The claimed upper endpoint. -/
  upper : ℕ
  /-- The actual rank is at least the lower endpoint. -/
  lower_le_finrank : lower ≤ Module.finrank ℤ W.toAffine.Point
  /-- The actual rank is at most the upper endpoint. -/
  finrank_le_upper : Module.finrank ℤ W.toAffine.Point ≤ upper

end VerifiedLcalc.EllipticCurve

namespace VerifiedLcalc

open EllipticCurve TauCeti

/-- A mathematically proved enclosure for an elliptic-curve regulator. -/
structure RegulatorFacts (W : WeierstrassCurve ℚ) [W.toAffine.IsElliptic] where
  /-- The center of the reported enclosure. -/
  reported : Rat
  /-- Its nonnegative absolute error radius. -/
  error : Rat
  /-- The error radius is nonnegative. -/
  error_nonneg : 0 ≤ error
  /-- TauCeti's regulator lies in the reported enclosure. -/
  within_error : |W.toAffine.regulator - (reported : ℝ)| ≤ (error : ℝ)
  /-- Optional exact rank-zero regulator value. -/
  exact_value : Option { value : ℝ // W.toAffine.regulator = value } := none

/-! ## Integral and rational points -/

/-- Indices into the checked integral coordinates and independence of precisely those points. -/
structure IndependentPointFacts {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (source : AffineMembership curve) where
  /-- Indices selecting the family from the integral-coordinate list. -/
  indices : List Nat
  /-- Every selected index refers to a supplied coordinate pair. -/
  indicesValid : ∀ i ∈ indices, i < source.coordinates.length
  /-- Integer linear independence of the corresponding rational points. -/
  independent : LinearIndependent ℤ (fun i : Fin indices.length =>
    source.rationalPoint ⟨indices[i], indicesValid _ (List.getElem_mem i.isLt)⟩)

/-- Positive exact orders aligned with the supplied rational point list. -/
structure TorsionGeneratorOrderFacts {curve : WeierstrassCurve ℚ} [curve.IsElliptic]
    (source : AffineMembership curve) where
  /-- The order list in the same index order as the points. -/
  orders : List ℕ
  /-- There is one order for every checked point. -/
  length_eq : orders.length = source.coordinates.length
  /-- Each order is positive. -/
  positive : ∀ n ∈ orders, 0 < n
  /-- The actual additive order of each supplied coordinate point. -/
  exactOrder : ∀ i : Fin source.coordinates.length,
    addOrderOf (source.point i) = orders.get (Fin.cast length_eq.symm i)

/-- A proved count of the rational points in the submitted generator list.
This records list length only; it makes no basis or generation claim. -/
structure GeneratorCountFacts (coordinates : List (Rat × Rat)) where
  /-- The submitted LMFDB generator count. -/
  count : ℕ
  /-- The coordinate list has exactly the claimed length. -/
  length_eq : coordinates.length = count

/-- Integral seed points and the complete set of integral y-coordinates over each seed's x. -/
structure IntegralYFiberFacts (curve : WeierstrassCurve ℤ) where
  /-- The supplied integral seed points, in input order. -/
  seeds : AffineMembership curve
  /-- The finite set of all integral y-coordinates at the indexed x-coordinate. -/
  fiber : Fin seeds.coordinates.length → Finset ℤ
  /-- The indexed fiber is exactly the set of solutions of the given equation at that x. -/
  complete : ∀ (i : Fin seeds.coordinates.length) (y : ℤ),
    y ∈ fiber i ↔ curve.toAffine.Equation (seeds.coordinates[i]).1 y

/-- Complete integral coordinates and their exact affine integral-point count. -/
structure CompleteIntegralPointFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- Reusable evidence for exhaustive abscissa support on the same model. -/
  support : IntegralXSupport curve
  /-- The distinct integral solutions, excluding the point at infinity. -/
  coordinates : Finset (ℤ × ℤ)
  /-- Membership is equivalent to satisfying the integral equation. -/
  complete : ∀ p : ℤ × ℤ, p ∈ coordinates ↔ curve.toAffine.Equation p.1 p.2
  /-- The exact number of affine integral points. -/
  count : ℕ
  /-- The checked count is the cardinality of the finite coordinate set. -/
  coordinates_card : coordinates.card = count
  /-- The affine integral points form a finite set, including when the count is zero. -/
  finite : Finite curve.integralPoints
  /-- The checked count is the cardinality in the rational point group. -/
  integralPoints_card : Nat.card curve.integralPoints = count

/-! ## Rational torsion -/

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

/-! ## Isogenies -/

/-- A degree-two edge between the specified rational equations, with its minimum-degree proof. -/
structure DegreeTwoIsogenyFact (source target : WeierstrassCurve ℤ) where
  /-- Nonsingularity of the rational source curve. -/
  source_elliptic : (source.baseChange ℚ).IsElliptic
  /-- Nonsingularity of the rational target curve. -/
  target_elliptic : (target.baseChange ℚ).IsElliptic
  /-- Rational isogeny between the two supplied equations. -/
  isogeny : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine
  /-- The exhibited isogeny has degree two. -/
  degree_eq : isogeny.degree = 2
  /-- The rational kernel has both points and has cardinality two. -/
  kernel_card : letI := source_elliptic
    Nat.card isogeny.ker = 2
  /-- Every rational isogeny between these equations has degree at least two. -/
  degree_le : ∀ φ : Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine,
    2 ≤ φ.degree

/-! ## Algebraic certificate fields -/

/-- Checked point lists, individual orders and algebraic lower bounds. -/
structure AlgebraicFacts (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- Membership on the supplied integral equation. -/
  integralPoints : Option (AffineMembership curve) := none
  /-- Complete integral y-fibers at the specified integral x-coordinates. -/
  integralYFibers : Option (IntegralYFiberFacts curve) := none
  /-- Exhaustive finite set and exact cardinality of all affine integral points. -/
  completeIntegralPoints : Option (CompleteIntegralPointFacts curve) := none
  /-- Membership for the supplied rational generator coordinates. -/
  generators : Option (AffineMembership (curve.baseChange ℚ)) := none
  /-- The checked `ngens` count for the supplied generator coordinates. -/
  generatorCount : Option (GeneratorCountFacts
    (generators.getD (AffineMembership.empty (curve.baseChange ℚ))).coordinates) := none
  /-- Membership for the supplied rational torsion generator coordinates. -/
  torsionGenerators : Option (AffineMembership (curve.baseChange ℚ)) := none
  /-- Exact orders of the listed torsion generators, when supplied and checked. -/
  torsionGeneratorOrders : Option (TorsionGeneratorOrderFacts
    (torsionGenerators.getD (AffineMembership.empty (curve.baseChange ℚ)))) := none
  /-- The supplied indexed points checked for infinite order. -/
  infiniteOrderPoints : Option
    (List (InfiniteOrderPointFact (integralPoints.getD (AffineMembership.empty curve)))) := none
  /-- The supplied family checked for integer independence. -/
  independentPoints : Option
    (IndependentPointFacts (integralPoints.getD (AffineMembership.empty curve))) := none
  /-- A proved lower bound for the rational Mordell–Weil rank. -/
  rankLowerBound : Option { n : ℕ //
    n ≤ Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point } := none
  /-- A proved lower and upper bound for the actual rational point group rank. -/
  rankBounds : Option (AlgebraicRankBounds (curve.baseChange ℚ)) := none
  /-- An exact algebraic Mordell–Weil rank, when the checked interval is a singleton. -/
  rank : Option { n : ℕ //
    Module.finrank ℤ (curve.baseChange ℚ).toAffine.Point = n } := none
  /-- A stored regulator enclosure checked from an exact algebraic rank of zero. -/
  regulator : Option (RegulatorFacts (curve.baseChange ℚ)) := none

end VerifiedLcalc
