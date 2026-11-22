module

public import VerifiedLcalc.Certification.CurveData
public import VerifiedLcalc.Certificate.ArithmeticFacts
public import VerifiedLcalc.Certificate.AnalyticFacts
public import VerifiedLcalc.EllipticCurve.PointIndependence
public import VerifiedLcalc.EllipticCurve.TorsionBound
public import Mathlib.GroupTheory.Torsion

/-!
# Checked data for one integral Weierstrass equation

An optional field is present when its corresponding evidence has been checked.
A membership certificate attests the supplied points. An algebraic rank bound
and a proof of independence carry their stated lower-bound conclusions.
-/

@[expose] public section

namespace VerifiedLcalc

/-- Exact invariants whose definitions specialize to the integral or rational equation. -/
structure RationalInvariantFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The sign of the integral equation's discriminant. -/
  discriminantSign : Option { s : ℤ // curve.Δ.sign = s } := none
  /-- The j-invariant of the rational curve. -/
  jInvariant : Option { j : ℚ // (curve.baseChange ℚ).j = j } := none
  /-- The truth value for integrality of the rational j-invariant. -/
  jIntegral : Option { b : Bool //
    IsLocalization.IsInteger ℤ (curve.baseChange ℚ).j ↔ b = true } := none

/-- Membership of every supplied coordinate pair on the given equation. -/
structure AffineMembership {R : Type*} [CommRing R] (curve : WeierstrassCurve R) where
  /-- The coordinates in the order supplied to the certifier. -/
  coordinates : List (R × R)
  /-- Each member of the list satisfies the equation. -/
  onCurve : ∀ x y, (x, y) ∈ coordinates → curve.toAffine.Equation x y

/-- A checked affine pair determines a point of an elliptic curve. -/
def AffineMembership.point {R : Type*} [CommRing R] [Nontrivial R]
    {curve : WeierstrassCurve R} [curve.IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) : curve.toAffine.Point :=
  .mk (facts.onCurve _ _ (List.getElem_mem i.isLt))

/-- Lift a checked integral pair to the rational point group. -/
def AffineMembership.rationalPoint {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) :
    (curve.baseChange ℚ).toAffine.Point :=
  curve.pointOfIntegralSolution (facts.coordinates[i]).1 (facts.coordinates[i]).2
    (facts.onCurve _ _ (List.getElem_mem i.isLt))

/-- The lifted point belongs to the set of integral points for the indexed equation. -/
theorem AffineMembership.rationalPoint_integral {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (facts : AffineMembership curve)
    (i : Fin facts.coordinates.length) :
    facts.rationalPoint i ∈ curve.integralPoints :=
  WeierstrassCurve.pointOfIntegralSolution_mem _ _ _ _

/-- Empty membership data, used when the integral-coordinate list is absent. -/
def AffineMembership.empty {R : Type*} [CommRing R]
    (curve : WeierstrassCurve R) : AffineMembership curve :=
  ⟨[], fun _ _ h => (List.not_mem_nil h).elim⟩

/-- A source index whose checked integral point has infinite order. -/
abbrev InfiniteOrderPointFact {curve : WeierstrassCurve ℤ} [(curve.baseChange ℚ).IsElliptic]
    (source : AffineMembership curve) :=
  { i : Fin source.coordinates.length // ¬ IsOfFinAddOrder (source.rationalPoint i) }

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

/-- The actual rational points selected by the verified source indices. -/
def IndependentPointFacts.points {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] {source : AffineMembership curve}
    (facts : IndependentPointFacts source)
    (i : Fin facts.indices.length) : (curve.baseChange ℚ).toAffine.Point :=
  source.rationalPoint ⟨facts.indices[i], facts.indicesValid _ (List.getElem_mem i.isLt)⟩

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

/-- Integral seed points and the complete set of integral y-coordinates over each seed's x. -/
structure IntegralYFiberFacts (curve : WeierstrassCurve ℤ) where
  /-- The supplied integral seed points, in input order. -/
  seeds : AffineMembership curve
  /-- The finite set of all integral y-coordinates at the indexed x-coordinate. -/
  fiber : Fin seeds.coordinates.length → Finset ℤ
  /-- The indexed fiber is exactly the set of solutions of the given equation at that x. -/
  complete : ∀ (i : Fin seeds.coordinates.length) (y : ℤ),
    y ∈ fiber i ↔ curve.toAffine.Equation (seeds.coordinates[i]).1 y

/-- Checked point lists, individual orders and algebraic lower bounds. -/
structure AlgebraicFacts (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- Membership on the supplied integral equation. -/
  integralPoints : Option (AffineMembership curve) := none
  /-- Complete integral y-fibers at the specified integral x-coordinates. -/
  integralYFibers : Option (IntegralYFiberFacts curve) := none
  /-- Membership for the supplied rational generator coordinates. -/
  generators : Option (AffineMembership (curve.baseChange ℚ)) := none
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
  /-- A proved lower bound for the rank of the rational point group. -/
  rankLowerBound : Option { n : ℕ //
    (n : Cardinal) ≤ Module.rank ℤ (curve.baseChange ℚ).toAffine.Point } := none

/-- A verified positive multiple of the whole torsion order
and an optional consistent raw claim. -/
structure TorsionDivisorFacts (curve : WeierstrassCurve ℤ) where
  /-- The odd primes and divisor supplied to the reduction check. -/
  evidence : TorsionBoundWitness
  /-- The stated divisor is the verified gcd of the two good-reduction point counts. -/
  checked : EllipticCurve.checkTorsionBound curve evidence.firstPrime evidence.secondPrime
    evidence.bound = true
  /-- The full torsion order divides this positive value. -/
  valid : Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) ∣
    evidence.bound ∧ 0 < evidence.bound
  /-- A supplied count consistent with the bound. -/
  consistentClaim : Option { n : ℕ // 0 < n ∧ n ∣ evidence.bound } := none

/-- The checked positive multiple of the full torsion order. -/
def TorsionDivisorFacts.bound {curve : WeierstrassCurve ℤ}
    (facts : TorsionDivisorFacts curve) : ℕ :=
  facts.evidence.bound

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

/-- Partial divisibility bounds and exact cardinality assertions for the torsion subgroup. -/
structure TorsionFacts (curve : WeierstrassCurve ℤ) where
  /-- Evidence that the full torsion order divides a checked positive bound. -/
  divisor : Option (TorsionDivisorFacts curve) := none
  /-- The exact cardinality of the whole torsion subgroup when determined. -/
  cardinality : Option { n : ℕ //
    Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n } := none
  /-- The checked cyclic structure, if requested and determined. -/
  cyclicStructure : Option (CyclicTorsionFacts curve) := none

/-- The family-indexed certificate exported by the verification command. -/
structure EllipticCertificate (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- Nonsingularity of the supplied integral equation. -/
  nonsingular : curve.Δ ≠ 0
  /-- Checked ring-valued invariants about the fixed equation. -/
  equationFacts : EllipticProofs curve
  /-- Checked integral or rational invariants. -/
  rational : RationalInvariantFacts curve
  /-- Checked points and algebraic lower bounds. -/
  algebraic : AlgebraicFacts curve
  /-- Checked arithmetic facts, including explicit-realization conditional facts. -/
  arithmetic : ArithmeticFacts curve
  /-- Checked numerical data and explicit-realization analytic results. -/
  analytic : AnalyticFacts curve
  /-- The checked full-group torsion facts. -/
  torsion : TorsionFacts curve

/-- The integral Weierstrass equation indexing the whole certificate. -/
def EllipticCertificate.equation {curve : WeierstrassCurve ℤ}
    [(curve.baseChange ℚ).IsElliptic] (_ : EllipticCertificate curve) : WeierstrassCurve ℤ :=
  curve

end VerifiedLcalc
