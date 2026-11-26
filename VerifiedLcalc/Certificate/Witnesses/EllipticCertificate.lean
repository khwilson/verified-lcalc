/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.Algebraic
public import VerifiedLcalc.Certificate.Witnesses.Analytic
public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes
public import VerifiedLcalc.Certificate.Witnesses.Invariants

/-! # Proof attachments and checked elliptic-curve certificates

* `IntegralCurveProofs` extends the equation invariant proofs with optional Mordell–Weil rank
  bounds over ℚ, exhaustive integral abscissa support, complete isogeny class evidence, and
  proofs of the real period, Tamagawa product, and analytic BSD quotient for the given equation.
* `EllipticCertificate` is the checked result indexed by the supplied integral equation and
  exported as `Name.certificate`. It carries nonsingularity, equation and rational invariants,
  algebraic, arithmetic, analytic, torsion and isogeny facts.
-/

@[expose] public section

namespace VerifiedLcalc

open EllipticCurve

/-- Lean proofs accepted alongside raw claims on an integral Weierstrass equation. -/
structure IntegralCurveProofs (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] extends EllipticProofs curve where
  /-- Proved endpoints of a Mordell–Weil rank interval on the rational curve. -/
  algebraicRank : Option (AlgebraicRankBounds (curve.baseChange ℚ)) := none
  /-- Exhaustive abscissa support for integral points on the supplied equation. -/
  integralXSupport : Option (IntegralXSupport curve) := none
  /-- Proof of the complete isogeny class and, optionally, its native LMFDB ordering. -/
  isogenyClass : Option (IsogenyClassEvidence curve) := none
  /-- Complete ordered isogeny classes at the actual conductor, with the subject's index. -/
  conductorClassRoster : Option (ConductorClassRoster curve) := none
  /-- Proof of every arithmetic coefficient used in the published trace fingerprint. -/
  traceHashCoefficients : Option (TraceHashCoefficients curve) := none
  /-- Conductor scope and complete singleton proofs for Cremona label checks. -/
  cremonaSingleton : Option (CremonaSingletonEvidence curve) := none
  /-- Actual non-CM and complete exceptional support evidence for the local Tate modules. -/
  nonmaxSupport : Option (NonmaxPrimeSupportFact curve) := none
  /-- Proof that the submitted matrices generate the entire finite torsion image. -/
  adelicGenerators :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (FiniteGaloisImageFact curve) := none
  /-- Exact simultaneous adelic image evidence for the submitted numeric fields or partial label. -/
  adelicImage :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (AdelicImageFact curve) := none
  /-- Exact residual image evidence for the submitted prime row. -/
  modPrimeImage :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (ModPrimeImageFact curve) := none
  /-- Exact residual image evidence for the submitted curve-level label list. -/
  modPrimeImages :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (ModPrimeImageListFact curve) := none
  /-- Exact comparison with the submitted prime-adic row. -/
  padicImage :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (PadicImageLabelFact curve) := none
  /-- Exact comparisons for the submitted list of prime-adic labels. -/
  padicImages :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (PadicImageListFact curve) := none
  /-- Verified entries of the source list of modular-curve labels for finite images. -/
  modulusImages :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (ModulusImageListFact curve) := none
  /-- Proof identifying the geometric endomorphism ring. -/
  complexMultiplication : Option (ComplexMultiplicationFacts curve) := none
  /-- Proof of a globally minimal integral model of a minimum-conductor quadratic twist. -/
  minimumQuadraticTwist : Option (MinimumQuadraticTwistEvidence curve) := none
  /-- Minimal model and exact conductor identification for a modified Szpiro enclosure. -/
  modifiedSzpiroRatio : Option (ModifiedSzpiroRatioEvidence curve) := none
  /-- Evidence of strict torsion growth in the field presented by the submitted polynomial. -/
  torsionGrowthField : Option (TorsionGrowthFieldFact curve) := none
  /-- An exact presentation of the full torsion group over the reported growth field. -/
  torsionGrowth : Option (TorsionGrowthFacts curve) := none
  /-- A proved height enclosure indexed by its ordered rational point list. -/
  canonicalHeights : Option (Σ points : (Σ n : ℕ,
    Fin n → (curve.baseChange ℚ).toAffine.Point), CanonicalHeightFacts points.2) := none
  /-- Proved position in the complete class's Faltings-height order. -/
  faltingsIndex : Option (FaltingsIndexFact curve) := none
  /-- Proved minimum modular map and its normalized differential and period image. -/
  modularParametrization : Option (ModularParametrizationFacts curve) := none
  /-- Proved complex period area, Faltings heights and class-relative area ratio. -/
  periodGeometry : Option (PeriodGeometryFacts curve) := none
  /-- Normalized cyclotomic interpolation and optional Iwasawa threshold evidence. -/
  iwasawa : Option (IwasawaFacts curve) := none
  /-- Proved enclosure for the full minimal real period. -/
  realPeriod : Option (RealPeriodFact curve) := none
  /-- Proved product of all intrinsic finite-place Tamagawa numbers. -/
  tamagawaProduct : Option (TamagawaProductFact curve) := none
  /-- Proved enclosure for the analytic BSD quotient under explicit realizations. -/
  analyticSha : Option (AnalyticShaFact curve) := none
  /-- Independent rank-one class regulator evidence before matching the reported ball. -/
  storedPadicRegulator : Option (StoredPadicRegulatorEvidence curve) := none

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
  torsion : TorsionWitness curve
  /-- Checked intrinsic subgroup order when the full rational torsion group is trivial. -/
  intrinsicTorsion : Option (IntrinsicTorsionFact curve) := none
  /-- The checked field presentation and absolute degree for one torsion growth row. -/
  torsionGrowthField : Option (TorsionGrowthFieldFact curve) := none
  /-- The full torsion subgroup with its invariant factors linked to one submitted row. -/
  torsionGrowth : Option (StoredTorsionGrowthFact curve) := none
  /-- A checked oriented rational isogeny edge and its integral target. -/
  isogeny : Option (Σ target : WeierstrassCurve ℤ, DegreeTwoIsogenyFact curve target) := none
  /-- The complete isogeny class with derived summaries and optional native LMFDB ordering. -/
  isogenyClass : Option (Σ facts : IsogenyClassFacts curve,
    Option (IsogenyClassOrdering facts.representatives)) := none
  /-- Checked LMFDB ordering indices and encoded labels for the supplied equation. -/
  lmfdbCatalogue : LmfdbCatalogueFacts curve := {}
  /-- A published trace fingerprint checked against every prescribed coefficient. -/
  traceHash : Option (TraceHashFact curve) := none
  /-- Cremona number and labels when the relevant orderings are singleton. -/
  cremonaCatalogue : Option (CremonaSingletonFacts curve) := none
  /-- Complete checked exceptional support for the non-CM curve. -/
  nonmaxPrimes : Option (NonmaxPrimeSupportFact curve) := none
  /-- Complete checked finite torsion image generated by the submitted matrices. -/
  adelicGenerators :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (FiniteGaloisImageFact curve) := none
  /-- The checked simultaneous adelic image, its proved invariants, and any partial label. -/
  adelicImage :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (AdelicImageCertificate curve) := none
  /-- The checked exact residual image for the submitted prime row. -/
  modPrimeImage :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (ModPrimeImageFact curve) := none
  /-- Checked exact residual images for the submitted list, with optional coverage. -/
  modPrimeImages :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (ModPrimeImageListFact curve) := none
  /-- The checked exact prime-adic image for the source row. -/
  padicImage :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (PadicImageLabelFact curve) := none
  /-- The checked source prime-adic labels and optional exceptional-prime coverage. -/
  padicImages :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (PadicImageListFact curve) := none
  /-- The verified sublist of modular-curve labels for finite images. -/
  modulusImages :
    letI := Classical.decEq (AlgebraicClosure ℚ)
    Option (ModulusImageListFact curve) := none
  /-- Complete exceptional triples under the semistable Serre recipe. -/
  serreInvariants : Option (SemistableSerreRecipeFact curve) := none
  /-- Checked identification of the geometric endomorphism ring. -/
  complexMultiplication : Option (ComplexMultiplicationFacts curve) := none
  /-- Checked minimum-conductor twist and its globally minimal integral equation. -/
  minimumQuadraticTwist : Option (MinimumQuadraticTwistEvidence curve) := none
  /-- Checked modified Szpiro ratio enclosure. -/
  modifiedSzpiroRatio : Option (ModifiedSzpiroRatioFacts curve) := none
  /-- Checked position in the complete class's Faltings-height order. -/
  faltingsIndex : Option (FaltingsIndexFact curve) := none
  /-- Minimum modular map with exact matches for the submitted modular claims. -/
  modularParametrization : Option (CertifiedModularParametrization curve) := none
  /-- Checked complex period area, Faltings heights and class-relative area ratio. -/
  periodGeometry : Option (PeriodGeometryFacts curve) := none
  /-- Checked Iwasawa rows and threshold, with the normalized modular-symbol model. -/
  iwasawa : Option (IwasawaFacts curve) := none
  /-- Checked full real period enclosure. -/
  realPeriod : Option (RealPeriodFact curve) := none
  /-- Checked product of the intrinsic finite-place Tamagawa numbers. -/
  tamagawaProduct : Option (TamagawaProductFact curve) := none
  /-- Checked analytic BSD quotient enclosure under explicit modular realizations. -/
  analyticSha : Option (AnalyticShaFact curve) := none
  /-- Checked rounded analytic quotient and any verified prime support. -/
  roundedAnalyticSha : Option (RoundedAnalyticShaFact curve) := none

end VerifiedLcalc
