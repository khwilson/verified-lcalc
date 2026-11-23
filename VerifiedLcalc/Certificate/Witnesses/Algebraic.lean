/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.InputData
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
public import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
public import TauCeti.NumberTheory.QuadraticOrder.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.RingTheory.AdjoinRoot

/-! # Rational and integral points, Mordell–Weil invariants and isogenies

* `EllipticCurve.AlgebraicRankBounds` records proved Mordell–Weil rank endpoints over ℚ.
  `RegulatorFacts` encloses the regulator of the nonsingular rational curve.
* `IndependentPointFacts` proves ℤ-linear independence of selected rational points.
  `TorsionWitness` ties orders and full-generation evidence to the supplied torsion generators.
* `IntegralYFiberFacts` enumerates all integral ordinates at each supplied abscissa.
  `CompleteIntegralPointFacts` uses exhaustive abscissa support to certify the full affine
  integral point set and its cardinality.
* `TorsionDivisorFacts` bounds the full rational torsion order by divisibility using good
  reduction point counts. `TorsionPresentation` identifies the full group as a product of
  invariant factors with specified images among the submitted points.
  `TorsionWitness` collects the generator family and optional group facts.
* `DegreeTwoIsogenyFact` and `IsogenyClassFacts` record minimum degrees of actual rational
  isogenies. The class witness also requires exhaustive and distinct representatives.
* `ComplexMultiplicationFacts` identifies the geometric endomorphism ring.
  `TorsionGrowthFacts` identifies a number field and its full base-changed torsion group.
  `CanonicalHeightFacts` encloses the canonical heights of indexed rational points.
* `MinimumQuadraticTwistFacts` specifies the twist relationship and minimum algorithmic conductor.
  The producer's tie rules require a separate comparison.
* `IntrinsicTorsionInput`, `ModularParametrizationInput`, and `FaltingsInput` record
  the respective catalogue reports.
* `AlgebraicFacts` collects optional checked points, orders, rank bounds, and regulator data.
-/

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

/-- Indices into a family of rational points and independence of precisely those points. -/
structure IndependentPointFacts {curve : WeierstrassCurve ℚ}
    [curve.IsElliptic] {n : Nat} (source : Fin n → curve.toAffine.Point) where
  /-- The number of selected points, certifying a rank lower bound. -/
  rank : Nat
  /-- The source index of each selected point. -/
  indices : Fin rank → Fin n
  /-- Integer linear independence of the corresponding rational points. -/
  independent : LinearIndependent ℤ (fun i => source (indices i))

/-- Integral seed points and the complete set of integral y-coordinates over each seed's x. -/
structure IntegralYFiberFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The number of supplied seeds. -/
  n : ℕ
  /-- The supplied integral seed points, in input order. -/
  seeds : Fin n → ↥curve.integralPoints
  /-- The finite set of integral y-coordinates at each seed's abscissa. -/
  fiber : Fin n → Finset ℤ
  /-- The indexed fiber is exactly the set of solutions at that seed's integer abscissa. -/
  complete : ∀ (i : Fin n) (y : ℤ),
    y ∈ fiber i ↔ curve.toAffine.Equation (seeds i).val.xCoord.num y

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

/-- A presentation of the full rational torsion subgroup by invariant factors whose standard
generators map to specified indices of the submitted family. -/
structure TorsionPresentation {curve : WeierstrassCurve ℚ} {n : ℕ}
    (source : Fin n → curve.toAffine.Point) where
  /-- The number of nontrivial invariant factors. -/
  k : ℕ
  /-- The order of each cyclic factor. -/
  factor : Fin k → ℕ
  /-- Each factor has order greater than one. -/
  factor_nontrivial : ∀ j, 1 < factor j
  /-- Earlier factors divide later factors. -/
  factors_divide : ∀ i j, i < j → factor i ∣ factor j
  /-- The submitted point index corresponding to each factor's standard generator. -/
  indices : Fin k → Fin n
  /-- The invariant-factor product is the full subgroup, with the specified generator images. -/
  realization :
    ∃ e : (∀ j, ZMod (factor j)) ≃+ AddCommGroup.torsion curve.toAffine.Point,
      ∀ j, (e (Pi.single j 1) : curve.toAffine.Point) = source (indices j)

/-- Exact distinct prime support of a finite rational torsion subgroup. -/
structure TorsionPrimeSupportFacts (curve : WeierstrassCurve ℤ) where
  /-- The distinct prime divisors of the exact group order. -/
  primes : List ℕ
  /-- Each prime appears at most once. -/
  nodup : primes.Nodup
  /-- The list contains exactly the prime divisors of the full subgroup order. -/
  exact_support : ∀ p, p ∈ primes ↔ p.Prime ∧
    p ∣ Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point)

/-- The submitted torsion-generator family and optional facts about the rational torsion
subgroup. Generator orders, generation and the invariant-factor presentation use the same
source indices. -/
structure TorsionWitness (curve : WeierstrassCurve ℤ) where
  /-- The submitted rational points in input order. -/
  generators : Option (Σ n : ℕ, Fin n → (curve.baseChange ℚ).toAffine.Point) := none
  /-- Positive exact orders at the submitted indices, when checked. -/
  orders :
    let source := generators.getD ⟨0, Fin.elim0⟩
    Option ((i : Fin source.1) → {m : ℕ+ // addOrderOf (source.2 i) = (m : ℕ)}) := none
  /-- The submitted points generate the full rational torsion subgroup, when proved. -/
  generation : Option (PLift
    (AddSubgroup.closure (Set.range (generators.getD ⟨0, Fin.elim0⟩).2) =
      AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point)) := none
  /-- The verified invariant factors and their images in the supplied family. -/
  presentation : Option (TorsionPresentation (generators.getD ⟨0, Fin.elim0⟩).2) := none
  /-- Evidence that the full torsion order divides a checked positive bound. -/
  divisor : Option (TorsionDivisorFacts curve) := none
  /-- The exact cardinality of the whole torsion subgroup when determined. -/
  cardinality : Option { n : ℕ //
    Nat.card (AddCommGroup.torsion (curve.baseChange ℚ).toAffine.Point) = n } := none
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

/-! ## Isogeny classes, complex multiplication and twists -/

/-- The common complete class data, with a lower bound for each ordered pair of representatives. -/
structure IsogenyClassData (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- The number of rational isomorphism classes. -/
  classSize : ℕ
  /-- The rational equations, in the same order as the rows and columns of the degree matrix. -/
  representatives : Fin classSize → WeierstrassCurve ℚ
  /-- Each representative is nonsingular. -/
  elliptic : ∀ i, (representatives i).IsElliptic
  /-- The row and column corresponding to the input curve. -/
  curveIndex : Fin classSize
  /-- The change of variables from the input curve to its representative. -/
  curveChange : WeierstrassCurve.VariableChange ℚ
  /-- The selected representative is rationally isomorphic to the input curve. -/
  curveChange_eq : curveChange • (curve.baseChange ℚ) = representatives curveIndex
  /-- No two distinct representatives are rationally isomorphic. -/
  distinct : ∀ i j (C : WeierstrassCurve.VariableChange ℚ),
    C • representatives i = representatives j → i = j
  /-- Any nonsingular rational equation admitting an isogeny from the input curve
  is rationally isomorphic to a listed representative. -/
  exhaustive : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
    Nonempty (Isogeny (curve.baseChange ℚ).toAffine W.toAffine) →
      ∃ (i : Fin classSize) (C : WeierstrassCurve.VariableChange ℚ), C • W = representatives i
  /-- The minimum isogeny degrees indexed by source and target, in that order. -/
  isogenyMatrix : Fin classSize → Fin classSize → ℕ
  /-- Every isogeny in that direction has degree at least the given entry. -/
  degree_min : ∀ i j (φ : Isogeny (representatives i).toAffine (representatives j).toAffine),
    isogenyMatrix i j ≤ φ.degree

/-- The supplied model proves existence of isogenies attaining each minimum degree. -/
structure IsogenyClassModel (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic]
    extends IsogenyClassData curve where
  /-- Each matrix entry is attained by a rational isogeny in its direction. -/
  attained : ∀ i j, ∃ φ : Isogeny (representatives i).toAffine (representatives j).toAffine,
    φ.degree = isogenyMatrix i j

/-- Reduced global minimal models in the lexicographic order used by LMFDB's labels.
This orders the rows and columns of the native LMFDB isogeny matrix. -/
structure IsogenyClassOrdering {n : ℕ}
    (representatives : Fin n → WeierstrassCurve ℚ) : Type where
  /-- The ordered equations are nonsingular. -/
  elliptic : ∀ i, (representatives i).IsElliptic
  /-- The representatives are the canonical reduced minimal Weierstrass equations over ℤ. -/
  reducedMinimal : ∀ i,
    letI : (representatives i).IsElliptic := elliptic i
    (representatives i).IsReducedMinimal
  /-- The five coefficients increase lexicographically. Reduced minimality ensures they
  lie in ℤ, where their order agrees with the order in ℚ used here. -/
  ordered : ∀ i j, i < j → List.Lex (· < ·)
    [(representatives i).a₁, (representatives i).a₂, (representatives i).a₃,
      (representatives i).a₄, (representatives i).a₆]
    [(representatives j).a₁, (representatives j).a₂, (representatives j).a₃,
      (representatives j).a₄, (representatives j).a₆]

/-- Complete distinct rational isomorphism representatives of the isogeny class of
`curve`, with its minimum-degree matrix and the row data for `curve`. -/
structure IsogenyClassFacts (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic]
    extends IsogenyClassData curve where
  /-- Every entry is attained by an actual isogeny in its direction. -/
  isogenies : ∀ i j, Isogeny (representatives i).toAffine (representatives j).toAffine
  /-- The entries equal the degrees of those isogenies. -/
  degree_eq : ∀ i j, (isogenies i j).degree = isogenyMatrix i j
  /-- The maximum entry over the entire class matrix. -/
  classDegree : ℕ
  /-- The maximum is attained. -/
  classDegree_mem : ∃ i j, isogenyMatrix i j = classDegree
  /-- The maximum bounds all entries. -/
  le_classDegree : ∀ i j, isogenyMatrix i j ≤ classDegree
  /-- The distinct minimum isogeny degrees read from the input curve's row. -/
  isogenyDegrees : Finset ℕ
  /-- The recorded degree set is precisely the set of entries in that row. -/
  isogenyDegrees_eq : isogenyDegrees = Finset.univ.image (isogenyMatrix curveIndex)

/-- Complete isogeny class evidence and optional LMFDB index ordering. -/
structure IsogenyClassEvidence (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- Pairwise distinct and exhaustive rational representatives with minimum degree proofs. -/
  model : IsogenyClassModel curve
  /-- Evidence of the native LMFDB order, required when comparing an ordered matrix. -/
  ordering : Option (IsogenyClassOrdering model.representatives) := none

/-- Exact description of the endomorphism ring over the separable closure of ℚ.
The zero code specifies the integer ring and a negative code specifies the quadratic
order of that discriminant. -/
structure ComplexMultiplicationFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The LMFDB CM code, either zero or an imaginary quadratic order discriminant. -/
  discriminant : ℤ
  /-- The geometric endomorphism ring agrees with the ring specified by the code. -/
  endomorphismRing :
    (discriminant = 0 ∧ Nonempty (ℤ ≃+* (curve.baseChange ℚ).GeometricEnd)) ∨
      (discriminant < 0 ∧
        ∃ h : discriminant % 4 = 0 ∨ discriminant % 4 = 1,
          Nonempty (QuadraticOrder.toSubalgebra discriminant h ≃+*
            (curve.baseChange ℚ).GeometricEnd))

/-- A quadratic twist attaining the minimum algorithmic conductor. The fundamental
discriminant and rational isomorphism identify the twist. Producer ordering among
equal-conductor candidates is a separate catalogue convention. -/
structure MinimumQuadraticTwistFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] where
  /-- The submitted integral equation of the candidate twist. -/
  equation : WeierstrassCurve ℤ
  /-- The submitted twist discriminant, with one denoting the trivial twist. -/
  discriminant : ℤ
  /-- The discriminant is fundamental. Mathlib includes one for the trivial twist. -/
  fundamental : discriminant.IsFundamentalDiscr
  /-- A rational change of variables from TauCeti's twist to the submitted model. -/
  change : WeierstrassCurve.VariableChange ℚ
  /-- Twisting by trace zero and norm minus the discriminant gives the same square class
  as the discriminant itself. The submitted model is rationally isomorphic to that twist. -/
  twist_eq : change • ((curve.baseChange ℚ).quadraticTwistOf 0 (-(discriminant : ℚ))) =
    equation.baseChange ℚ
  /-- The reported twist is nonsingular over the rationals. -/
  elliptic : (equation.baseChange ℚ).IsElliptic
  /-- No quadratic twist of the original curve has smaller algorithmic conductor norm. -/
  conductor_minimal :
    letI := elliptic
    ∀ (d : ℚ), d ≠ 0 →
      let W := (curve.baseChange ℚ).quadraticTwistOf 0 (-d)
      ∀ (hW : W.IsElliptic),
        letI := hW
        Ideal.absNorm ((equation.baseChange ℚ).algorithmicConductor ℤ) ≤
          Ideal.absNorm (W.algorithmicConductor ℤ)

/-! ## Torsion over number fields and canonical heights -/

/-- The full torsion group over the field presented by a specified irreducible rational
polynomial. This describes one field and makes no primitive-growth or exhaustivity claim. -/
structure TorsionGrowthFacts (curve : WeierstrassCurve ℤ) where
  /-- The defining polynomial decoded from its ascending coefficient list. -/
  polynomial : Polynomial ℚ
  /-- Irreducibility makes Mathlib's root-adjoining algebra a field. -/
  irreducible : Irreducible polynomial
  /-- The absolute degree of that field over ℚ. -/
  degree : ℕ
  /-- The reported degree equals the field degree. -/
  degree_eq : Module.finrank ℚ (AdjoinRoot polynomial) = degree
  /-- Nonsingularity after base change to the presented field. -/
  elliptic :
    letI : Fact (Irreducible polynomial) := ⟨irreducible⟩
    (curve.baseChange (AdjoinRoot polynomial)).IsElliptic
  /-- The invariant factors in divisibility order, omitting factors of one. -/
  torsion : List ℕ
  /-- All factors have order at least two. -/
  factors_nontrivial : ∀ n ∈ torsion, 2 ≤ n
  /-- Earlier invariant factors divide later ones. -/
  factors_divide : torsion.Pairwise (· ∣ ·)
  /-- The product of cyclic groups is additively equivalent to the full torsion subgroup. -/
  equivalence :
    letI : Fact (Irreducible polynomial) := ⟨irreducible⟩
    (∀ i : Fin torsion.length, ZMod (torsion.get i)) ≃+
      AddCommGroup.torsion (curve.baseChange (AdjoinRoot polynomial)).toAffine.Point

/-- Rational enclosures for the actual heights of the supplied rational points, in
TauCeti's logarithmic x-coordinate height normalization. The point indexing tracks list
order and is independent of any basis or generation claim. -/
structure CanonicalHeightFacts {curve : WeierstrassCurve ℚ} [curve.IsElliptic] {n : ℕ}
    (source : Fin n → curve.toAffine.Point) where
  /-- The rational enclosure center for each point, in coordinate-list order. -/
  reported : Fin n → ℚ
  /-- The rational absolute error radius for each point. -/
  error : Fin n → ℚ
  /-- Each radius is nonnegative. -/
  error_nonneg : ∀ i, 0 ≤ error i
  /-- The canonical height of each indexed point lies in its reported enclosure. -/
  within_error : ∀ i,
    |(source i).canonicalHeight - (reported i : ℝ)| ≤ (error i : ℝ)

/-! ## Input records pending mathematical specifications -/

/-- Input only. The claimed order of the radical of the rational torsion pairing. -/
structure IntrinsicTorsionInput (curve : WeierstrassCurve ℤ) where
  /-- The decoded `intrinsic_torsion` value. -/
  order : ℕ

/-- Input only. The degree and differential scaling of a modular parametrization,
and the producer's status code for optimality. -/
structure ModularParametrizationInput (curve : WeierstrassCurve ℤ) where
  /-- The claimed modular parametrization degree, when present. -/
  degree : Option ℕ := none
  /-- The claimed Manin constant, when present. -/
  maninConstant : Option ℕ := none
  /-- The producer's optimality code, which can express ambiguity among candidates. -/
  optimalityCode : Option ℕ := none

/-- Input only. The reported Faltings heights and class-relative data. -/
structure FaltingsInput (curve : WeierstrassCurve ℤ) where
  /-- The reported Faltings height in the producer's normalization. -/
  height : Option ℚ := none
  /-- The reported stable Faltings height. -/
  stableHeight : Option ℚ := none
  /-- The proposed Néron lattice index relative to the least-height curve in the class. -/
  ratio : Option ℕ := none
  /-- The producer's position in the Faltings-height ordering of the class. -/
  orderingIndex : Option ℕ := none

/-! ## Algebraic certificate fields -/

/-- Checked point lists, individual orders and algebraic lower bounds. -/
structure AlgebraicFacts (curve : WeierstrassCurve ℤ) [(curve.baseChange ℚ).IsElliptic] where
  /-- Membership on the supplied integral equation. -/
  integralPoints : Option (Σ n : ℕ, Fin n → ↥curve.integralPoints) := none
  /-- Complete integral y-fibers at the specified integral x-coordinates. -/
  integralYFibers : Option (IntegralYFiberFacts curve) := none
  /-- Exhaustive finite set and exact cardinality of all affine integral points. -/
  completeIntegralPoints : Option (CompleteIntegralPointFacts curve) := none
  /-- Membership for the supplied rational generator coordinates. -/
  generators : Option (Σ n : ℕ, Fin n → (curve.baseChange ℚ).toAffine.Point) := none
  /-- The supplied indexed integral points checked for infinite order. -/
  infiniteOrderPoints :
    let source := integralPoints.getD ⟨0, Fin.elim0⟩
    Option (List { i : Fin source.1 // ¬ IsOfFinAddOrder (source.2 i).val }) := none
  /-- The indexed family from the integral coordinates checked for integer independence. -/
  independentPoints :
    let source := integralPoints.getD ⟨0, Fin.elim0⟩
    Option (IndependentPointFacts (fun i => (source.2 i).val)) := none
  /-- The indexed family from the rational generator list checked for integer independence. -/
  independentGeneratorPoints :
    Option (IndependentPointFacts (generators.getD ⟨0, Fin.elim0⟩).2) := none
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
