/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import Lean.Data.Name
import Lean.Data.NameMap.Basic

/-! The source field routes used by the EC/Q certificate decoder and command.
Several database columns share the same interpretation. When the interpretation
changes with the table or JSON scope, the routes are recorded independently. -/

public section

namespace VerifiedLcalc.FieldCatalogue

open Lean

private def qualify (name : Name) : Name := `VerifiedLcalc ++ name

-- The names are resolved by the certificate contract audit. This lets the decoder use
-- the catalogue without importing the command or its mathematical proof dependencies.
local notation "vl[" name "]" => qualify name

/-- One accepted interpretation of a JSON field, including proof prerequisites. -/
structure Path where
  /-- JSON keys from the root to the field. An array node denotes each submitted row. -/
  json : List String
  /-- Fully qualified input projections, from the witness down to the field. -/
  claim : List Name
  /-- Relative name of the generated check or checked fact under the certificate name. -/
  check : Option Name
  /-- The verifier, its soundness lemma, or the command handler for an inline check.
  The contract audit resolves these references in the complete command environment. -/
  verify : Option Name
  /-- The first name selects the component of `EllipticCertificate`. Subsequent names
  identify its data and proof fields, including sibling fields of the same checked record.
  A report-only route has an empty list. -/
  output : List Name
  /-- Required typed witness data or caller-supplied proof projections. -/
  prerequisites : List Name
  /-- Conditions under which the route proves the native interpretation. -/
  scope : String
  /-- Relative name of the checked fact used by certificate assembly, if routed here. -/
  fact : Option Name := none
  deriving Repr

/-- One table-qualified column in the EC/Q schema. -/
structure Column where
  /-- Table name, including the `ec_` prefix. -/
  table : String
  /-- Column name in the native schema. -/
  field : String
  /-- Supported encodings or documented report-only cases. -/
  paths : List Path
  deriving Repr

private def checkedPath (json : List String) (claim : List Name) (check : Name)
    (output : List Name) (scope : String) (prerequisites : List Name := [])
    (verify : Name := vl[`CertifyEC.certifyStoredInvariants])
    (fact : Option Name := none) : Path :=
  ⟨json, claim, some check, some verify, output, prerequisites, scope, fact⟩

private def reportPath (json : List String) (claim : List Name) (scope : String) : Path :=
  ⟨json, claim, none, none, [], [], scope, none⟩

private def aliases (path : Path) (container : String) : List Path :=
  [path, { path with json := container :: path.json }]

private def arith := vl[`EllipticCertificate.arithmetic]
private def minimalModel := vl[`ArithmeticFacts.minimalModel]
private def modular := vl[`ArithmeticFacts.modular]
private def analytic := vl[`EllipticCertificate.analytic]
private def algebraic := vl[`EllipticCertificate.algebraic]

private def adelic : List Name :=
  [vl[`EllipticCertificate.adelicImage], vl[`AdelicImageCertificate.facts]]

private structure Route where
  tables : List String
  field : String
  paths : List Path

private def flat (tables : List String) (field : String) (claim check : Name)
    (output : List Name) (scope : String) (prerequisites : List Name := [])
    (verify : Name := vl[`CertifyEC.certifyStoredInvariants])
    (fact : Option Name := none) : Route :=
  ⟨tables, field, [checkedPath [field] [claim] check output scope prerequisites verify fact]⟩

private def localRow (field : String) (claim check : Name)
    (output : List Name) (scope : String) (prerequisites : List Name)
    (verify : Name) : Route :=
  ⟨["localdata"], field, aliases
    (checkedPath [field] [vl[`EllipticWitness.localInvariants], claim] check
      output scope prerequisites verify) "local_invariants"⟩

private def padicRow (field : String) (claim : List Name) (output : List Name)
    (scope : String) : Route :=
  ⟨["padic"], field, aliases
    (checkedPath [field] claim `stored_padic_regulator_fact
      ([analytic, vl[`AnalyticFacts.storedPadicRegulator]] ++ output) scope
      [vl[`IntegralCurveProofs.storedPadicRegulator]] vl[`Certification.storedPadicRegulatorFact])
    "padic_regulator"⟩

private def displayedPadic (field : String) (claim : Name) (output : List Name)
    (scope : String) : Path :=
  checkedPath ["padic_regulator", field] [vl[`EllipticWitness.padicRegulator], claim]
    `padic_regulator_fact ([analytic, vl[`AnalyticFacts.padicRegulator]] ++ output)
    scope [] vl[`Certification.rankZeroPadicRegulatorFact]

private def stored : List Route :=
  [
    flat ["curvedata"] "Ciso" vl[`EllipticWitness.cremonaIso] `Ciso
      [vl[`EllipticCertificate.cremonaCatalogue], vl[`CremonaSingletonFacts.isoLabel]]
      "Complete singleton conductor roster in the published range."
      [vl[`IntegralCurveProofs.cremonaSingleton]]
      (verify := vl[`CertifyEC.certifyCremona]),
    flat ["curvedata"] "Clabel" vl[`EllipticWitness.cremonaLabel] `Clabel
      [vl[`EllipticCertificate.cremonaCatalogue], vl[`CremonaSingletonFacts.curveLabel]]
      "Complete singleton conductor roster and singleton isogeny class in the published range."
      [vl[`IntegralCurveProofs.cremonaSingleton]]
      (verify := vl[`CertifyEC.certifyCremona]) (fact := some `cremona_catalogue_fact),
    flat ["curvedata"] "Cnumber" vl[`EllipticWitness.cremonaNumber] `Cnumber
      [vl[`EllipticCertificate.cremonaCatalogue], vl[`CremonaSingletonFacts.number]]
      "Complete singleton isogeny class in the published range."
      [vl[`IntegralCurveProofs.cremonaSingleton]]
      (verify := vl[`CertifyEC.certifyCremona]),
    flat ["curvedata"] "abc_quality" vl[`EllipticWitness.abcQuality] `abc_quality
      [vl[`EllipticCertificate.rational], vl[`RationalInvariantFacts.abcQuality],
        vl[`AbcQualityFacts.within_error]]
      "Explicit radius and complete factorization, with j distinct from 0 and 1728."
      (verify := vl[`Certification.abcQualityValid]),
    flat ["curvedata"] "absD" vl[`EllipticWitness.minimalDiscriminantAbs] `minimal_discriminant_abs
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.minimalDiscriminantAbs]]
      "Absolute discriminant of the checked globally minimal equation."
      [vl[`EllipticWitness.minimality]]
      (verify := vl[`Certification.minimal_discriminant_abs_of_witness]),
    flat ["curvedata"] "adelic_genus" vl[`EllipticWitness.adelicGenus] `adelic_genus
      (adelic ++ [vl[`AdelicImageFact.genus], vl[`AdelicGenusFact.correct]])
      "Euler characteristic of the effective compactified quotient of the exact simultaneous image."
      [vl[`IntegralCurveProofs.adelicImage]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]),
    flat ["curvedata"] "adelic_index" vl[`EllipticWitness.adelicIndex] `adelic_index
      (adelic ++ [vl[`AdelicImageFact.index]])
      "Index in the full integral adelic matrix group."
      [vl[`IntegralCurveProofs.adelicImage]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]),
    flat ["curvedata"] "adelic_level" vl[`EllipticWitness.adelicLevel] `adelic_level
      (adelic ++ [vl[`AdelicImageFact.level]])
      "Least positive modulus with full kernel containment."
      [vl[`IntegralCurveProofs.adelicImage]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]),
    flat ["curvedata"] "ainvs" vl[`EllipticWitness.equation] `nonsingular
      [vl[`EllipticCertificate.nonsingular]]
      "Integral equation indexing the certificate and its nonzero discriminant proof."
      (verify := vl[`CertifyECData.certify]),
    flat ["curvedata"] "analytic_rank" vl[`EllipticWitness.catalogueAnalyticRank]
      `catalogue_analytic_rank
      [analytic, vl[`AnalyticFacts.rank], vl[`ConditionalAnalyticRank.correct]]
      "Requires independently checked numerical evidence of exact order zero or one."
      [vl[`EllipticWitness.minimality], vl[`EllipticWitness.localData]]
      (verify := vl[`CertifyEC.certifyCatalogueRank]),
    flat ["curvedata"] "bad_primes" vl[`EllipticWitness.badPrimes] `bad_reduction_primes
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.badPrimes]]
      "Complete distinct primes of bad reduction of the minimal model."
      [vl[`EllipticWitness.minimality]] (verify := vl[`Certification.bad_reduction_prime_iff]),
    flat ["curvedata", "classdata"] "class_deg" vl[`EllipticWitness.classDegree] `class_deg
      [vl[`EllipticCertificate.isogenyClass], `Sigma.fst, vl[`IsogenyClassFacts.classDegree],
        vl[`IsogenyClassFacts.classDegree_mem], vl[`IsogenyClassFacts.le_classDegree]]
      "Maximum of the complete matrix of minimum degrees."
      [vl[`IntegralCurveProofs.isogenyClass]]
      (verify := vl[`CertifyEC.certifyIsogenyClass]),
    flat ["curvedata", "classdata"] "class_size" vl[`EllipticWitness.classSize] `class_size
      [vl[`EllipticCertificate.isogenyClass], `Sigma.fst, vl[`IsogenyClassFacts.toIsogenyClassData],
        vl[`IsogenyClassData.classSize]]
      "Exact number of rational isomorphism types with exhaustive class evidence."
      [vl[`IntegralCurveProofs.isogenyClass]]
      (verify := vl[`CertifyEC.certifyIsogenyClass]),
    flat ["curvedata"] "cm" vl[`EllipticWitness.complexMultiplication] `cm
      [vl[`EllipticCertificate.complexMultiplication],
        vl[`ComplexMultiplicationFacts.endomorphismRing]]
      "Geometric endomorphism ring as an order of given discriminant, or the integers for zero."
      [vl[`IntegralCurveProofs.complexMultiplication]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]) (fact := some `cm_fact),
    flat ["curvedata", "classdata", "mwbsd", "localdata", "galrep"] "conductor"
      vl[`EllipticWitness.conductor] `conductor
      [arith, modular, vl[`ModularArithmeticFacts.conductor]]
      "Level of an arithmetic modular realization. The standalone theorem uses modularity."
      [vl[`EllipticWitness.minimality], vl[`EllipticWitness.localData]]
      (verify := vl[`Certification.conductor_of_arithmetic_witness]),
    flat ["curvedata"] "degree" vl[`EllipticWitness.modularDegree] `modular_degree
      [vl[`EllipticCertificate.modularParametrization], vl[`CertifiedModularParametrization.degree]]
      "Least degree of the rational modular parametrization at the actual conductor."
      [vl[`IntegralCurveProofs.modularParametrization]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]) (fact := some `modular_parametrization_fact),
    flat ["curvedata"] "elladic_images" vl[`EllipticWitness.padicImages] `elladic_images
      [vl[`EllipticCertificate.padicImages], vl[`PadicImageListFact.entries],
        vl[`PadicImageLabelFact.correct]]
      "Listed exact integral Tate-module images, with separate optional exhaustive support."
      [vl[`IntegralCurveProofs.padicImages]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `elladic_images_fact),
    flat ["curvedata"] "faltings_height" vl[`EllipticWitness.faltingsHeight] `faltings_height
      [vl[`EllipticCertificate.periodGeometry], vl[`PeriodGeometryFacts.height],
        vl[`PeriodGeometryEnclosure.within_error]]
      "Enclosure of the Faltings height on the verified globally minimal model."
      [vl[`IntegralCurveProofs.periodGeometry]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]),
    flat ["curvedata"] "faltings_index" vl[`EllipticWitness.faltingsIndex] `faltings_index
      [vl[`EllipticCertificate.faltingsIndex], vl[`FaltingsIndexFact.index],
        vl[`FaltingsIndexFact.mem_predecessors]]
      "Exact predecessor count on the complete class, with ties in native order."
      [vl[`IntegralCurveProofs.faltingsIndex]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]) (fact := some `faltings_index_fact),
    flat ["curvedata"] "faltings_ratio" vl[`EllipticWitness.faltingsRatio] `faltings_ratio
      [vl[`EllipticCertificate.periodGeometry], vl[`PeriodGeometryFacts.ratio],
        vl[`FaltingsRatioFact.area_eq]]
      "Exact ratio of the attained maximal area to the input area in the complete class."
      [vl[`IntegralCurveProofs.periodGeometry]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]),
    flat ["curvedata"] "intrinsic_torsion" vl[`EllipticWitness.intrinsicTorsion]
      `intrinsic_torsion_fact
      [vl[`EllipticCertificate.intrinsicTorsion], vl[`IntrinsicTorsionFact.torsion_card]]
      "The cardinality is one when the entire rational torsion subgroup is trivial." (fact := some
      `intrinsic_torsion_fact),
    flat ["curvedata"] "iso_nlabel" vl[`EllipticWitness.isoNlabel] `iso_nlabel
      [vl[`EllipticCertificate.lmfdbCatalogue], vl[`LmfdbCatalogueFacts.classIndex]]
      "Zero-based isogeny-class index in the ordered conductor roster."
      [vl[`IntegralCurveProofs.conductorClassRoster]]
      (verify := vl[`CertifyEC.certifyLmfdbCatalogue]),
    flat ["curvedata"] "isogeny_degrees" vl[`EllipticWitness.isogenyDegrees] `isogeny_degrees
      [vl[`EllipticCertificate.isogenyClass], `Sigma.fst, vl[`IsogenyClassFacts.isogenyDegrees]]
      "Set of minimum isogeny degrees from the subject to the complete class."
      [vl[`IntegralCurveProofs.isogenyClass]]
      (verify := vl[`CertifyEC.certifyIsogenyClass]),
    flat ["curvedata"] "jinv" vl[`EllipticWitness.jInvariant] `j_invariant
      [vl[`EllipticCertificate.rational], vl[`RationalInvariantFacts.jInvariant]]
      "Exact rational j-invariant." (verify := vl[`Certification.j_invariant_of_exact_formula]),
    flat ["curvedata", "classdata"] "lmfdb_iso" vl[`EllipticWitness.lmfdbIso] `lmfdb_iso
      [vl[`EllipticCertificate.lmfdbCatalogue], vl[`LmfdbCatalogueFacts.isoLabel]]
      "Class label from the conductor and the ordered roster."
      [vl[`IntegralCurveProofs.conductorClassRoster]]
      (verify := vl[`CertifyEC.certifyLmfdbCatalogue]),
    flat ["curvedata", "mwbsd", "iwasawa", "torsion_growth", "localdata", "galrep"] "lmfdb_label"
      vl[`EllipticWitness.lmfdbLabel] `lmfdb_label
      [vl[`EllipticCertificate.lmfdbCatalogue], vl[`LmfdbCatalogueFacts.curveLabel]]
      "Curve label from the ordered conductor roster and complete canonical curve order."
      [vl[`IntegralCurveProofs.conductorClassRoster], vl[`IntegralCurveProofs.isogenyClass]]
      (verify := vl[`CertifyEC.certifyLmfdbCatalogue]),
    flat ["curvedata"] "lmfdb_number" vl[`EllipticWitness.lmfdbNumber] `lmfdb_number
      [vl[`EllipticCertificate.lmfdbCatalogue], vl[`LmfdbCatalogueFacts.number]]
      "One-based position in the complete reduced minimal equation order."
      [vl[`IntegralCurveProofs.isogenyClass]]
      (verify := vl[`CertifyEC.certifyLmfdbCatalogue]),
    flat ["curvedata"] "manin_constant" vl[`EllipticWitness.maninConstant] `manin_constant
      [vl[`EllipticCertificate.modularParametrization],
        vl[`CertifiedModularParametrization.maninConstant]]
      "Positive scaling of the minimal Néron differential under a minimum-degree map."
      [vl[`IntegralCurveProofs.modularParametrization]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]),
    flat ["curvedata"] "min_quad_twist_ainvs" vl[`EllipticWitness.minimumTwistEquation]
      `min_quad_twist_ainvs
      [vl[`EllipticCertificate.minimumQuadraticTwist], vl[`MinimumQuadraticTwistEvidence.minimum],
        vl[`MinimumQuadraticTwistFacts.equation]]
      "Minimal model of a least-conductor twist. Producer ties need separate evidence."
      [vl[`IntegralCurveProofs.minimumQuadraticTwist]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]) (fact := some
      `minimum_quadratic_twist_evidence),
    flat ["curvedata"] "min_quad_twist_disc" vl[`EllipticWitness.minimumTwistDiscriminant]
      `min_quad_twist_disc
      [vl[`EllipticCertificate.minimumQuadraticTwist], vl[`MinimumQuadraticTwistEvidence.minimum],
        vl[`MinimumQuadraticTwistFacts.discriminant]]
      "Fundamental discriminant of a minimum-conductor twist."
      [vl[`IntegralCurveProofs.minimumQuadraticTwist]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]),
    flat ["curvedata"] "modell_images" vl[`EllipticWitness.modPrimeImages] `modell_images
      [vl[`EllipticCertificate.modPrimeImages], vl[`ModPrimeImageListFact.images],
        vl[`ModPrimeImageFact.conjugate]]
      "Exact conjugacy classes for listed residual images. Optional exhaustive non-CM support."
      [vl[`IntegralCurveProofs.modPrimeImages]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `modell_images_fact),
    flat ["curvedata"] "modm_images" vl[`EllipticWitness.modulusImages] `modm_images
      [vl[`EllipticCertificate.modulusImages], vl[`ModulusImageListFact.entries],
        vl[`ModulusImageLabelFact.correct]]
      "Ordered sublist of finite images, with level, index and genus for supported prefixes."
      [vl[`IntegralCurveProofs.modulusImages]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `modm_images_fact),
    flat ["curvedata"] "nonmax_primes" vl[`EllipticWitness.nonmaxPrimes] `nonmax_primes
      [vl[`EllipticCertificate.nonmaxPrimes], vl[`NonmaxPrimeSupportFact.complete]]
      "Complete exceptional support of integral images for non-CM curves."
      [vl[`IntegralCurveProofs.nonmaxSupport]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `nonmax_prime_support),
    flat ["curvedata"] "nonmax_rad" vl[`EllipticWitness.nonmaxRadical] `nonmax_rad
      [vl[`EllipticCertificate.nonmaxPrimes], vl[`NonmaxPrimeSupportFact.primes]]
      "Exact product over the proved exceptional support."
      [vl[`IntegralCurveProofs.nonmaxSupport]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]),
    flat ["curvedata"] "num_bad_primes" vl[`EllipticWitness.numBadPrimes] `num_bad_primes
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.numBadPrimes]]
      "Number of distinct prime divisors of the minimal discriminant."
      [vl[`EllipticWitness.minimality]],
    flat ["curvedata"] "num_int_pts" vl[`EllipticWitness.numIntegralPoints] `num_int_pts
      [algebraic, vl[`AlgebraicFacts.completeIntegralPoints],
        vl[`CompleteIntegralPointFacts.integralPoints_card]]
      "Exact count given exhaustive abscissa support. Otherwise checks a lower bound."
      [vl[`IntegralCurveProofs.integralXSupport]]
      (verify := vl[`CertifyEC.certifyCompleteIntegralPoints]),
    flat ["curvedata"] "optimality" vl[`EllipticWitness.optimality] `optimality
      [vl[`EllipticCertificate.modularParametrization],
        vl[`CertifiedModularParametrization.optimality]]
      "Binary codes compare the full integral period image. Larger codes are reports."
      [vl[`IntegralCurveProofs.modularParametrization]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]),
    flat ["curvedata"] "potential_good_reduction" vl[`EllipticWitness.potentialGoodReduction]
      `potential_good_reduction
      [arith, vl[`ArithmeticFacts.potentialGoodReduction]]
      "Boolean equivalence with potential good reduction at every prime."
      (verify := vl[`Certification.potential_good_reduction_iff_of_check]),
    flat ["curvedata"] "rank" vl[`EllipticWitness.algebraicRank] `algebraic_rank
      [algebraic, vl[`AlgebraicFacts.rank]]
      "Exact algebraic rank from a singleton proved interval."
      [vl[`IntegralCurveProofs.algebraicRank]]
      (verify := vl[`CertifyEC.certifyProofAttachment]),
    flat ["curvedata"] "regulator" vl[`EllipticWitness.regulator] `regulator_facts
      [algebraic, vl[`AlgebraicFacts.regulator], vl[`RegulatorFacts.within_error]]
      "Enclosure of the actual regulator when algebraic rank is proved zero."
      [vl[`IntegralCurveProofs.algebraicRank]]
      (verify := vl[`Certification.rankZeroRegulatorValid]),
    flat ["curvedata"] "semistable" vl[`EllipticWitness.semistable] `semistable
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.semistable]]
      "Boolean equivalence with semistable reduction."
      [vl[`EllipticWitness.minimality]]
      (verify := vl[`EllipticCurve.semistable_iff_coprime_of_isGlobalMinimal]),
    flat ["curvedata"] "serre_invariants" vl[`EllipticWitness.serreInvariants]
      `serre_invariants
      [vl[`EllipticCertificate.serreInvariants], vl[`SemistableSerreRecipeFact.exactRows]]
      "Serre's exact exceptional triples for semistable curves with good reduction at two."
      [vl[`EllipticWitness.minimality]] (fact := some `serre_invariants_fact),
    flat ["curvedata"] "sha" vl[`EllipticWitness.sha] `sha_rounds
      [vl[`EllipticCertificate.roundedAnalyticSha], vl[`RoundedAnalyticShaFact.rounds]]
      "Analytic quotient strictly inside the rounding cell of a positive integer."
      [vl[`IntegralCurveProofs.analyticSha]]
      (verify := vl[`CertifyEC.certifyBSDFacts]) (fact := some `rounded_analytic_sha_fact),
    flat ["curvedata"] "sha_primes" vl[`EllipticWitness.shaPrimes] `sha_prime_report_matches
      [vl[`EllipticCertificate.roundedAnalyticSha], vl[`RoundedAnalyticShaFact.primes]]
      "Complete distinct prime support of the checked rounded analytic quotient."
      [vl[`IntegralCurveProofs.analyticSha], vl[`EllipticWitness.sha]]
      (verify := vl[`CertifyEC.certifyBSDFacts]) (fact := some `rounded_analytic_sha_fact),
    flat ["curvedata"] "signD" vl[`EllipticWitness.discriminantSign] `discriminant_sign
      [vl[`EllipticCertificate.rational], vl[`RationalInvariantFacts.discriminantSign]]
      "Sign of the discriminant of the supplied equation.",
    flat ["curvedata"] "squarefree_disc" vl[`EllipticWitness.squarefreeDiscriminant]
      `squarefree_discriminant
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.squarefreeDiscriminant]]
      "Boolean equivalence with squarefree absolute minimal discriminant."
      [vl[`EllipticWitness.minimality]]
      (verify := vl[`Certification.squarefree_discriminant_iff_nodup]),
    flat ["curvedata"] "stable_faltings_height" vl[`EllipticWitness.stableFaltingsHeight]
      `stable_faltings_height
      [vl[`EllipticCertificate.periodGeometry], vl[`PeriodGeometryFacts.stableHeight],
        vl[`PeriodGeometryEnclosure.within_error]]
      "Enclosure of the Faltings height with the stable-height logarithmic correction."
      [vl[`IntegralCurveProofs.periodGeometry]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]),
    flat ["curvedata"] "szpiro_ratio" vl[`EllipticWitness.modifiedSzpiroRatio] `szpiro_ratio_valid
      [vl[`EllipticCertificate.modifiedSzpiroRatio], vl[`ModifiedSzpiroRatioFacts.within_error]]
      "Logarithmic enclosure on the minimal equation with proved algorithmic conductor norm."
      [vl[`IntegralCurveProofs.modifiedSzpiroRatio]]
      (verify := vl[`Certification.modifiedSzpiroRatioValid]) (fact := some `szpiro_ratio_fact),
    flat ["curvedata"] "torsion" vl[`EllipticWitness.torsion] `torsion
      [vl[`EllipticCertificate.torsion], vl[`TorsionWitness.cardinality]]
      "Exact order of rational torsion when proved. Larger bounds alone give divisibility."
      [vl[`EllipticWitness.torsionBound]],
    flat ["curvedata"] "torsion_primes" vl[`EllipticWitness.torsionPrimes]
      `torsion_primes_value_valid
      [vl[`EllipticCertificate.torsion], vl[`TorsionWitness.primeSupport],
        vl[`TorsionPrimeSupportFacts.exact_support]]
      "Exact ascending distinct prime support of the proved full rational torsion order."
      [vl[`EllipticWitness.torsionBound]] (verify := vl[`TorsionPrimeSupportFacts.exact_support]),
    flat ["curvedata"] "torsion_structure" vl[`EllipticWitness.torsionStructure]
      `torsion_presentation
      [vl[`EllipticCertificate.torsion], vl[`TorsionWitness.presentation],
        vl[`TorsionPresentation.realization]]
      "Full cyclic or two-factor presentation with identified submitted generators."
      [vl[`EllipticWitness.torsionBound]],
    flat ["classdata"] "anlist" vl[`EllipticWitness.dirichletCoefficients] `dirichlet_coefficients
      [arith, vl[`ArithmeticFacts.dirichletCoefficients]]
      "Consecutive actual coefficients from a₁ after checking and removing native a₀."
      [vl[`EllipticWitness.minimality]]
      (verify := vl[`Certification.coefficients_of_minimal_witness]),
    flat ["classdata"] "aplist" vl[`EllipticWitness.primeCoefficients] `ap_correct
      [arith, vl[`ArithmeticFacts.primeCoefficients]]
      "Prime coefficients of the curve with checked local minimality at the given indices." (verify
      := vl[`EllipticWitness.primeCoefficientsValid_sound]),
    flat ["classdata"] "isogeny_matrix" vl[`EllipticWitness.isogenyMatrix] `isogeny_matrix
      [vl[`EllipticCertificate.isogenyClass], `Sigma.fst, vl[`IsogenyClassFacts.toIsogenyClassData],
        vl[`IsogenyClassData.isogenyMatrix], vl[`IsogenyClassFacts.degree_eq],
        vl[`IsogenyClassData.degree_min]]
      "Complete matrix of minimum degrees in canonical LMFDB order."
      [vl[`IntegralCurveProofs.isogenyClass]]
      (verify := vl[`CertifyEC.certifyIsogenyClass]),
    flat ["classdata"] "trace_hash" vl[`EllipticWitness.traceHash] `trace_hash_value_valid
      [vl[`EllipticCertificate.traceHash], vl[`TraceHashFact.correct]]
      "Weighted residue from the complete prescribed prime coefficient list."
      [vl[`IntegralCurveProofs.traceHashCoefficients]] (verify := vl[`Certification.traceHashFact])
        (fact := some `trace_hash_fact),
    flat ["mwbsd"] "area" vl[`EllipticWitness.area] `area
      [vl[`EllipticCertificate.periodGeometry], vl[`PeriodGeometryFacts.area],
        vl[`PeriodGeometryEnclosure.within_error]]
      "Enclosure of the Euclidean covolume of the minimal normalized complex period lattice."
      [vl[`IntegralCurveProofs.periodGeometry]]
      (verify := vl[`CertifyEC.certifyGeometryFacts]) (fact := some `period_geometry_fact),
    flat ["mwbsd"] "gens" vl[`EllipticWitness.generatorCoordinates] `generators.points_on_curve
      [algebraic, vl[`AlgebraicFacts.generators]]
      "Ordered rational affine points with curve membership."
      (verify := vl[`EllipticWitness.affineCoordinatesValid_sound]),
    flat ["mwbsd"] "heights" vl[`EllipticWitness.canonicalHeights] `heights_report_matches
      [algebraic, vl[`AlgebraicFacts.heights], vl[`CanonicalHeightFacts.within_error]]
      "Canonical height enclosures for the actual submitted generators in order."
      [vl[`IntegralCurveProofs.canonicalHeights]]
      (verify := vl[`CertifyEC.certifyExtensionData]) (fact := some `canonical_heights_fact),
    flat ["mwbsd"] "ngens" vl[`EllipticWitness.generatorCount] `generators.count_valid
      [algebraic, vl[`AlgebraicFacts.generatorCount]]
      "Length of the checked rational generator list."
      [vl[`EllipticWitness.generatorCoordinates]]
      (verify := vl[`CertifyECData.certify]),
    flat ["mwbsd"] "rank_bounds" vl[`EllipticWitness.algebraicRankBounds] `algebraic_rank_bounds
      [algebraic, vl[`AlgebraicFacts.rankBounds],
        vl[`EllipticCurve.AlgebraicRankBounds.lower_le_finrank],
        vl[`EllipticCurve.AlgebraicRankBounds.finrank_le_upper]]
      "Both endpoints bound the Mordell–Weil rank."
      [vl[`IntegralCurveProofs.algebraicRank]]
      (verify := vl[`CertifyEC.certifyProofAttachment]),
    flat ["mwbsd"] "real_period" vl[`EllipticWitness.realPeriod] `real_period_report_matches
      [vl[`EllipticCertificate.realPeriod], vl[`RealPeriodFact.correct]]
      "Enclosure for the full minimal real period including every real component."
      [vl[`IntegralCurveProofs.realPeriod]]
      (verify := vl[`CertifyEC.certifyBSDFacts]) (fact := some `real_period_fact),
    flat ["mwbsd"] "sha_an" vl[`EllipticWitness.analyticSha] `sha_an_report_matches
      [vl[`EllipticCertificate.analyticSha], vl[`AnalyticShaFact.correct]]
      "Enclosure of the analytic BSD quotient with exact order and positive denominator."
      [vl[`IntegralCurveProofs.analyticSha]]
      (verify := vl[`CertifyEC.certifyBSDFacts]) (fact := some `analytic_sha_fact),
    flat ["mwbsd"] "special_value" vl[`EllipticWitness.specialLValue] `special_value_valid
      [analytic, vl[`AnalyticFacts.specialValue], vl[`SpecialLValueFacts.correct]]
      "Enclosure of the Taylor leading coefficient at a proved exact order zero or one."
      [vl[`EllipticWitness.minimality], vl[`EllipticWitness.localData]]
      (verify := vl[`CertifyEC.analyticFactsTerm]),
    flat ["mwbsd"] "tamagawa_product" vl[`EllipticWitness.tamagawaProduct]
      `tamagawa_product_report_matches
      [vl[`EllipticCertificate.tamagawaProduct], vl[`TamagawaProductFact.correct]]
      "Exact product of intrinsic finite-local Tamagawa factors."
      [vl[`IntegralCurveProofs.tamagawaProduct]]
      (verify := vl[`CertifyEC.certifyBSDFacts]) (fact := some `tamagawa_product_fact),
    flat ["mwbsd"] "torsion_generators" vl[`EllipticWitness.torsionGeneratorCoordinates]
      `torsion_generators.points_on_curve
      [vl[`EllipticCertificate.torsion], vl[`TorsionWitness.generators]]
      "Ordered rational points, with exact torsion orders when separately verified."
      (verify := vl[`EllipticWitness.affineCoordinatesValid_sound]),
    flat ["mwbsd"] "xcoord_integral_points" vl[`EllipticWitness.integralFiberRoots]
      `integral_fiber_roots_valid
      [algebraic, vl[`AlgebraicFacts.integralYFibers], vl[`IntegralYFiberFacts.complete]]
      "Complete integral y-fiber at each listed abscissa."
      (verify := vl[`EllipticWitness.mem_integralYFiber_iff]),
    flat ["galrep"] "adelic_gens" vl[`EllipticWitness.adelicGenerators] `adelic_gens
      [vl[`EllipticCertificate.adelicGenerators], vl[`FiniteGaloisImageFact.generators],
        vl[`FiniteGaloisImageFact.correct]]
      "Generators of the exact geometric torsion image at the reported modulus."
      [vl[`IntegralCurveProofs.adelicGenerators]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `adelic_generator_fact),
    flat ["galrep"] "adelic_image" vl[`EllipticWitness.adelicImage] `adelic_image
      [vl[`EllipticCertificate.adelicImage], vl[`AdelicImageCertificate.partialLabel]]
      "Prime-zero partial label with proved level, index and genus, leaving the suffix unspecified."
      [vl[`IntegralCurveProofs.adelicImage]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `adelic_image_certificate),
    flat ["galrep"] "elladic_image" vl[`EllipticWitness.padicImage] `elladic_image
      [vl[`EllipticCertificate.padicImage], vl[`PadicImageLabelFact.correct]]
      "Full integral Tate-module image for the supported local subgroup label."
      [vl[`IntegralCurveProofs.padicImage]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `elladic_image_fact),
    flat ["galrep"] "modell_image" vl[`EllipticWitness.modPrimeImage] `modell_image
      [vl[`EllipticCertificate.modPrimeImage], vl[`ModPrimeImageFact.conjugate]]
      "Exact residual image up to conjugacy for the supported subgroup label."
      [vl[`IntegralCurveProofs.modPrimeImage]]
      (verify := vl[`CertifyEC.certifyGaloisFacts]) (fact := some `modell_image_fact),
    flat ["iwasawa"] "iwdata" vl[`EllipticWitness.iwasawaData] `iwasawa_fact
      [vl[`EllipticCertificate.iwasawa], vl[`IwasawaFacts.rows], vl[`IwasawaSeriesOrder.correct]]
      "Selected ordinary, signed, or additive evidence. Unknown rows stay as reports."
      [vl[`IntegralCurveProofs.iwasawa]] (verify := vl[`IwasawaPrimeEvidence.encoding])
      (fact := some `iwasawa_fact),
    flat ["iwasawa"] "iwp0" vl[`EllipticWitness.iwasawaThreshold] `iwp0
      [vl[`EllipticCertificate.iwasawa], vl[`IwasawaFacts.threshold],
        vl[`IwasawaThresholdEvidence.vanishing]]
      "Checked positive threshold for all good primes at or above it. Zero stays a sentinel."
      [vl[`IntegralCurveProofs.iwasawa]] (verify := vl[`IwasawaThresholdEvidence.vanishing]),
    localRow "prime" vl[`LocalReductionClaim.prime] `local_invariants
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.localRows],
        vl[`LocalReductionClaim.Spec]]
      "Primality for a checked local row." [vl[`EllipticWitness.minimality]]
      vl[`LocalReductionClaim.check_correct],
    localRow "discriminant_valuation" vl[`LocalReductionClaim.discriminantValuation]
      `local_invariants
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.localRows],
        vl[`LocalReductionClaim.Spec]]
      "Exact valuation of the absolute minimal discriminant." [vl[`EllipticWitness.minimality]]
      vl[`LocalReductionClaim.check_correct],
    localRow "j_denominator_valuation" vl[`LocalReductionClaim.jDenominatorValuation]
      `local_invariants
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.localRows],
        vl[`LocalReductionClaim.Spec]]
      "Exact valuation of the reduced rational j-denominator." [vl[`EllipticWitness.minimality]]
      vl[`LocalReductionClaim.check_correct],
    localRow "reduction_type" vl[`LocalReductionClaim.reductionType] `local_invariants
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.localRows],
        vl[`LocalReductionClaim.Spec]]
      "Arithmetic additive, split or nonsplit code." [vl[`EllipticWitness.minimality]]
      vl[`LocalReductionClaim.check_correct],
    localRow "conductor_valuation" vl[`LocalReductionClaim.conductorValuation] `conductor_valuation
      [arith, modular, vl[`ModularArithmeticFacts.conductorValuations]]
      "Prime exponent in the checked arithmetic realization's level."
      [vl[`EllipticWitness.minimality], vl[`EllipticWitness.localData],
      vl[`EllipticWitness.conductor]] vl[`Certification.factorization_of_prime_exponent_check],
    localRow "kodaira_symbol" vl[`LocalReductionClaim.kodairaSymbol] `kodaira_symbols
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.kodaira], vl[`LocalKodairaFact.correct]]
      "Exact good and multiplicative codes. Additive codes exclude all multiplicative symbols only."
      [vl[`EllipticWitness.minimality]] vl[`LocalReductionClaim.kodaira_correct],
    localRow "tamagawa_number" vl[`LocalReductionClaim.tamagawaNumber] `tamagawa_numbers
      [arith, vl[`ArithmeticFacts.tamagawa], vl[`LocalTamagawaFact.correct]]
      "Exact intrinsic factor at good, I₁, I₂ or supported tame III reduction." []
      vl[`LocalReductionClaim.tamagawa_correct],
    localRow "root_number" vl[`LocalReductionClaim.rootNumber] `local_root_numbers
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.localRootNumbers],
        vl[`LocalRootNumberFact.correct]]
      "Exact local arithmetic sign on a minimal model with the needed transcripts."
      [vl[`EllipticWitness.minimality], vl[`EllipticWitness.localData]]
      vl[`LocalReductionClaim.rootNumber_correct],
    padicRow "lmfdb_iso" [vl[`EllipticWitness.padicRegulatorClassLabel]]
      [vl[`StoredPadicRegulatorFact.classLabel_eq]]
      "Ordered singleton isogeny class and reduced minimal representative.",
    padicRow "p" [vl[`EllipticWitness.padicRegulator], vl[`PadicRegulatorClaim.p]]
      [vl[`StoredPadicRegulatorFact.prime_eq], vl[`StoredPadicRegulatorFact.good],
        vl[`StoredPadicRegulatorFact.ordinary]]
      "Prime above three with good ordinary reduction and rank-one sigma evidence.",
    padicRow "prec" [vl[`EllipticWitness.padicRegulator], vl[`PadicRegulatorClaim.prec]]
      [vl[`StoredPadicRegulatorFact.report], vl[`PadicRegulatorReport.prec],
        vl[`StoredPadicRegulatorFact.contains]]
      "Absolute precision of the ball containing the rank-one regulator.",
    padicRow "val" [vl[`EllipticWitness.padicRegulator], vl[`PadicRegulatorClaim.val]]
      [vl[`StoredPadicRegulatorFact.valuation_eq]]
      "Exact valuation of the nonzero normalized rank-one height.",
    padicRow "unit" [vl[`EllipticWitness.padicRegulator], vl[`PadicRegulatorClaim.unit]]
      [vl[`StoredPadicRegulatorFact.report], vl[`PadicRegulatorReport.unit],
        vl[`StoredPadicRegulatorFact.normalized], vl[`StoredPadicRegulatorFact.contains]]
      "Canonical unit residue in the stated ball.",
    ⟨["torsion_growth"], "field", [checkedPath ["torsion_growth", "field"]
      [vl[`EllipticWitness.torsionGrowthField], vl[`TorsionGrowthFieldClaim.coefficients]]
      `torsion_growth_polynomial_matches
      [vl[`EllipticCertificate.torsionGrowthField], vl[`TorsionGrowthFieldFact.polynomial],
        vl[`TorsionGrowthFieldFact.irreducible], vl[`TorsionGrowthFieldFact.growth]]
      "Irreducible polynomial and a new torsion point over its field."
      [vl[`IntegralCurveProofs.torsionGrowthField]]
      (verify := vl[`CertifyEC.certifyExtensionData]) (fact := some `torsion_growth_field_fact)]⟩,
    ⟨["torsion_growth"], "degree", [checkedPath ["torsion_growth", "degree"]
      [vl[`EllipticWitness.torsionGrowthField], vl[`TorsionGrowthFieldClaim.degree]]
      `torsion_growth_degree_matches
      [vl[`EllipticCertificate.torsionGrowthField], vl[`TorsionGrowthFieldFact.degree_eq]]
      "Absolute degree of the field with a proved new torsion point."
      [vl[`IntegralCurveProofs.torsionGrowthField]]
      (verify := vl[`TorsionGrowthFieldFact.degree_eq])]⟩,
    ⟨["galrep"], "prime", [checkedPath ["prime"] [vl[`EllipticWitness.modPrimeImage], `Prod.fst]
      `modell_image_prime
      [vl[`EllipticCertificate.modPrimeImage], vl[`ModPrimeImageFact.prime]]
      "Primality for a residual image row." (verify := vl[`CertifyEC.certifyGaloisFacts]),
      checkedPath ["prime"] [vl[`EllipticWitness.padicImage], `Prod.fst] `elladic_image_prime
        [vl[`EllipticCertificate.padicImage], vl[`PadicImageLabelFact.prime]]
        "Primality for a prime-adic image row.",
      checkedPath ["prime"] [vl[`EllipticWitness.adelicImage], `Prod.fst] `adelic_image_prime
        [vl[`EllipticCertificate.adelicImage], vl[`AdelicImageCertificate.partialLabel]]
        "The adelic row uses the sentinel zero." (verify := vl[`CertifyEC.certifyGaloisFacts]),
      reportPath ["prime"] [vl[`PrimeGaloisImageClaim.prime]]
        "An isolated prime report has no image proof."]⟩,
    ⟨["torsion_growth"], "torsion", [
      checkedPath ["torsion_growth", "torsion"]
        [vl[`EllipticWitness.torsionGrowthFactors], vl[`EllipticWitness.torsionGrowthField]]
        `torsion_growth_factors_match
        [vl[`EllipticCertificate.torsionGrowth], vl[`StoredTorsionGrowthFact.polynomial_eq],
          vl[`StoredTorsionGrowthFact.factors_eq], vl[`StoredTorsionGrowthFact.equivalence]]
        "Exact invariant factors of the full torsion subgroup over the row's field."
        [vl[`IntegralCurveProofs.torsionGrowth]]
        (verify := vl[`CertifyEC.certifyExtensionData]) (fact := some `torsion_growth_fact)]⟩ ]

private def enclosureEvidence : List Path :=
  let members := [
    (vl[`EllipticWitness.abcQuality], "error", vl[`AbcQualityClaim.error]),
    (vl[`EllipticWitness.abcQuality], "factors", vl[`AbcQualityClaim.factors]),
    (vl[`EllipticWitness.canonicalHeights], "errors", vl[`CanonicalHeightsClaim.errors]),
    (vl[`EllipticWitness.regulator], "error", vl[`RegulatorClaim.error]),
    (vl[`EllipticWitness.specialLValue], "error", vl[`SpecialLValueClaim.error])]
  let decimalClaims := [vl[`EllipticWitness.area], vl[`EllipticWitness.faltingsHeight],
    vl[`EllipticWitness.stableFaltingsHeight], vl[`EllipticWitness.modifiedSzpiroRatio],
    vl[`EllipticWitness.realPeriod], vl[`EllipticWitness.analyticSha]]
  let members := members ++
    decimalClaims.map fun claim => (claim, "error", vl[`DecimalEnclosureClaim.error])
  let paths := stored.flatMap (·.paths)
  members.filterMap fun (claim, key, member) => do
    let path ← paths.find? (fun path => path.claim == [claim])
    let [field] := path.json | none
    return { path with
      json := [field ++ "_evidence", key], claim := [claim, member], fact := none }

/-- Project JSON extensions outside the stored LMFDB schema. -/
def extensions : List Path :=
  [
    checkedPath ["ap"] [vl[`EllipticWitness.primeCoefficients]] `ap_correct
      [arith, vl[`ArithmeticFacts.primeCoefficients]]
      "Explicit prime-indexed coefficient pairs."
      (verify := vl[`EllipticWitness.primeCoefficientsValid_sound]),
    checkedPath ["algebraic_rank"] [vl[`EllipticWitness.algebraicRank]] `algebraic_rank
      [algebraic, vl[`AlgebraicFacts.rank]]
      "Explicit alias for the algebraic rank."
      [vl[`IntegralCurveProofs.algebraicRank]]
      (verify := vl[`CertifyEC.certifyProofAttachment]),
    checkedPath ["global_root_number"] [vl[`EllipticWitness.rootNumber]] `root_number
      [arith, modular, vl[`ModularArithmeticFacts.rootNumber]]
      "Global sign of the arithmetic modular realization."
      [vl[`EllipticWitness.minimality], vl[`EllipticWitness.localData]]
      (verify := vl[`Certification.root_number_of_arithmetic_witness]),
    checkedPath ["binvs"] [vl[`EllipticWitness.bInvariants]] `b_invariants
      [vl[`EllipticCertificate.equationFacts], vl[`EllipticProofs.bInvariants]]
      "Exact b-invariants of the supplied equation."
      (verify := vl[`CertifyEC.certifyStoredInvariants]),
    checkedPath ["cinvs"] [vl[`EllipticWitness.cInvariants]] `c_invariants
      [vl[`EllipticCertificate.equationFacts], vl[`EllipticProofs.cInvariants]]
      "Exact c-invariants of the supplied equation."
      (verify := vl[`CertifyEC.certifyStoredInvariants]),
    checkedPath ["discriminant"] [vl[`EllipticWitness.discriminant]] `discriminant
      [vl[`EllipticCertificate.equationFacts], vl[`EllipticProofs.discriminant]]
      "Exact discriminant of the supplied equation."
      (verify := vl[`CertifyEC.certifyStoredInvariants]),
    checkedPath ["j_integral"] [vl[`EllipticWitness.jIntegral]] `j_integral
      [vl[`EllipticCertificate.rational], vl[`RationalInvariantFacts.jIntegral]]
      "Boolean equivalence with integrality of the rational j-invariant."
      (verify := vl[`Certification.j_integral_iff_of_check]),
    checkedPath ["integral_points"] [vl[`EllipticWitness.integralCoordinates]] `point_integral
      [algebraic, vl[`AlgebraicFacts.integralPoints]]
      "Membership of the submitted coordinates."
      (verify := vl[`EllipticWitness.integralCoordinatesValid_sound]),
    checkedPath ["torsion_bound"] [vl[`EllipticWitness.torsionBound]] `torsion_bound
      [vl[`EllipticCertificate.torsion], vl[`TorsionWitness.divisor]]
      "Divisibility by the gcd of the two checked good-prime point counts."
      (verify := vl[`Certification.torsionDivisorFacts_of_check]),
    checkedPath ["torsion_generator_orders"] [vl[`EllipticWitness.torsionGeneratorOrders]]
      `torsion_generators.exact_order
      [vl[`EllipticCertificate.torsion], vl[`TorsionWitness.orders]]
      "Exact orders on the indexed submitted generators."
      (verify := vl[`EllipticWitness.exactOrderCheck_sound]),
    checkedPath ["infinite_order_points"] [vl[`EllipticWitness.infiniteOrderPoints]]
      `infinite_order_count_eq
      [algebraic, vl[`AlgebraicFacts.infiniteOrderPoints]]
      "Infinite order at the submitted indices."
      (verify := vl[`CertifyEC.certifyPointFields]),
    checkedPath ["independent_points"] [vl[`EllipticWitness.independentPoints]]
      `algebraic_rank_lower_bound
      [algebraic, vl[`AlgebraicFacts.independentPoints]]
      "Integer independence proved for the submitted integral point indices."
      (verify := vl[`CertifyEC.certifyPointFields]),
    checkedPath ["independent_generator_points"] [vl[`EllipticWitness.independentGeneratorPoints]]
      `algebraic_rank_lower_bound
      [algebraic, vl[`AlgebraicFacts.independentGeneratorPoints]]
      "Integer independence proved for the submitted generator indices."
      (verify := vl[`CertifyEC.certifyPointFields]),
    checkedPath ["isogeny_edge"] [vl[`EllipticWitness.isogenyEdge]] `isogeny_minimum_degree
      [vl[`EllipticCertificate.isogeny], vl[`DegreeTwoIsogenyFact.isLeast_degree]]
      "Minimum isogeny degree two for the specified source and target."
      (verify := vl[`CertifyEC.certifyIsogenyEdge]),
    checkedPath ["minimality"] [vl[`EllipticWitness.minimality]] `global_minimal
      [arith, minimalModel, vl[`MinimalModelArithmeticFacts.minimality]]
      "Global minimality from the complete discriminant factorization.",
    checkedPath ["local_data"] [vl[`EllipticWitness.localData]] `local_data_valid
      [arith, vl[`ArithmeticFacts.localData]]
      "Validity of the supplied local transcripts."
      (verify := vl[`CertifyEC.certifyLocalData]),
    checkedPath ["analytic_witness"] [vl[`EllipticWitness.centralResult]] `payload_correct
      [analytic, vl[`AnalyticFacts.central], vl[`AnalyticFacts.rank]]
      "Complete central payload, with exact rank when mathematical analytic evidence is available."
      (verify := vl[`CertifyEC.certifyAnalytic]),
    checkedPath ["analytic_witness"] [vl[`EllipticWitness.derivativeResult]] `payload_correct
      [analytic, vl[`AnalyticFacts.derivative], vl[`AnalyticFacts.rank]]
      "Complete derivative payload, with exact rank given the needed mathematical evidence."
      (verify := vl[`CertifyEC.certifyAnalytic]),
    displayedPadic "p" vl[`PadicRegulatorClaim.p]
      [vl[`RankZeroPadicRegulatorFact.good],
        vl[`RankZeroPadicRegulatorFact.ordinary]]
      "For a curve-level report without class label, prove good ordinary reduction and rank zero.",
    displayedPadic "prec" vl[`PadicRegulatorClaim.prec]
      [vl[`RankZeroPadicRegulatorFact.report], vl[`PadicRegulatorReport.prec],
        vl[`RankZeroPadicRegulatorFact.contains]]
      "The submitted ball at this absolute precision contains the rank-zero determinant.",
    displayedPadic "val" vl[`PadicRegulatorClaim.val]
      [vl[`RankZeroPadicRegulatorFact.report], vl[`PadicRegulatorReport.val],
        vl[`RankZeroPadicRegulatorFact.contains]]
      "A curve-level rank-zero display must use valuation zero.",
    displayedPadic "unit" vl[`PadicRegulatorClaim.unit]
      [vl[`RankZeroPadicRegulatorFact.report], vl[`PadicRegulatorReport.unit],
        vl[`RankZeroPadicRegulatorFact.normalized]]
      "A curve-level rank-zero display must use unit one.",
    checkedPath ["analytic_witness", "arithmetic", "minimality"] [vl[`EllipticWitness.minimality]]
      `global_minimal [arith, minimalModel, vl[`MinimalModelArithmeticFacts.minimality]]
      "Global minimality from the legacy numerical witness's factorization."
      (verify := vl[`CertifyEC.certifyLocalData]),
    checkedPath ["analytic_witness", "arithmetic"] [vl[`EllipticWitness.localData]]
      `local_data_valid [arith, vl[`ArithmeticFacts.localData]]
      "Legacy numerical witness transcripts at two and three."
      (verify := vl[`CertifyEC.certifyLocalData]),
    checkedPath ["subject", "ainvs"] [vl[`EllipticWitness.equation]] `nonsingular
      [vl[`EllipticCertificate.nonsingular]] "Equation in an explicit subject object."
      (verify := vl[`CertifyECData.certify]),
    checkedPath ["analytic_witness", "subject", "ainvs"] [vl[`EllipticWitness.equation]]
      `nonsingular
      [vl[`EllipticCertificate.nonsingular]] "Equation in a nested numerical witness subject."
      (verify := vl[`CertifyECData.certify]),
    checkedPath ["analytic_witness", "ainvs"] [vl[`EllipticWitness.equation]] `nonsingular
      [vl[`EllipticCertificate.nonsingular]] "Equation in a nested numerical witness."
      (verify := vl[`CertifyECData.certify]) ] ++ enclosureEvidence

/-- All 101 table-qualified EC/Q columns, with shared mappings expanded by table. -/
def columns : List Column :=
  stored.flatMap fun r => r.tables.map fun table => ⟨"ec_" ++ table, r.field, r.paths⟩

private def allPaths : List Path := extensions ++ stored.flatMap (·.paths)

private def flatSourceKeys : NameMap String :=
  allPaths.foldl (fun keys path =>
    match path.json, path.claim with
    | [key], [.str receiver field] =>
      if receiver == vl[`EllipticWitness] then keys.insert (.mkSimple field) key else keys
    | _, _ => keys) {}

private def checkers : NameMap Name :=
  allPaths.foldl (fun result path =>
    match path.claim, path.verify with
    | [.str receiver field], some checker =>
      if receiver == vl[`EllipticWitness] then result.insert (.mkSimple field) checker else result
    | _, _ => result) {}

private def outputFacts : NameMap Name :=
  allPaths.foldl (fun result path =>
    match path.claim.head?, path.fact with
    | some (.str receiver field), some fact =>
      if receiver == vl[`EllipticWitness] then result.insert (.mkSimple field) fact else result
    | _, _ => result) {}

/-- Preferred JSON key for a direct, unqualified `EllipticWitness` field.
Scoped or multi-claim decoders use their complete routes instead. -/
def sourceKey (witnessField : Name) : Option String :=
  flatSourceKeys.find? witnessField

/-- Verifier for the primary path of an input field.
A path implemented by an inline comparison names its command handler. -/
def checker (witnessField : Name) : Option Name :=
  checkers.find? witnessField

/-- Name of the checked declaration assembled into the aggregate for this field. -/
def outputFact (witnessField : Name) : Option Name :=
  outputFacts.find? witnessField

end VerifiedLcalc.FieldCatalogue
