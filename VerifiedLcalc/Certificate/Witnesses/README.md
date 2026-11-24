# LMFDB fields and their Lean witnesses

Start with [`EllipticWitness`](EllipticWitness.lean) for input to `certify_ec` and [`EllipticCertificate`](EllipticCertificate.lean) for the checked output, `Name.certificate`. The tables identify each field’s Lean structure and say what evidence it holds. For `ainvs`, the equation itself is the input that indexes the certificate.

The index covers **85 distinct column names** across **101 table-qualified columns** in the eight EC/ℚ tables, excluding the database row identifier `id`. Each name appears once. The table column omits the `ec_` prefix. [LMFDB schema for 37.a1](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)

All 85 names have a Lean record. **Checked** means `certify_ec` can populate the indicated evidence in the stated cases. **Structure** means a record specifies a proof obligation for a future constructor. **Report** records supplied data and may enforce local conditions such as primality. **Metadata** records catalogue provenance. **Mixed** gives the status for each table or case in the row. Command coverage is **80 of 85**. [Certification guide](../../../docs/LMFDB_INVARIANTS.md) · [EC/ℚ roadmap](../../../docs/roadmaps/LMFDB_Q_CERTIFICATION.md)

## Curve data (`ec_curvedata`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `Ciso` | `curvedata` | Checked | [`CremonaSingletonFacts.isoLabel`](Algebraic.lean). The conductor and suffix `a` with a complete singleton conductor roster. |
| `Clabel` | `curvedata` | Checked | [`CremonaSingletonFacts.curveLabel`](Algebraic.lean). The conductor and suffix `a1` with both complete singleton orderings. |
| `Cnumber` | `curvedata` | Checked | [`CremonaSingletonFacts.number`](Algebraic.lean). One with a complete singleton rational isogeny class. |
| `abc_quality` | `curvedata` | Checked | [`AbcQualityFacts.within_error`](Invariants.lean). The reported rational and its error enclose the curve’s abc quality, using a checked factorization with j distinct from 0 and 1728. |
| `absD` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.minimalDiscriminantAbs`](FinitePrimes.lean). Absolute discriminant of a model proved globally minimal. |
| `adelic_genus` | `curvedata` | Checked with evidence | [`EllipticWitness.adelicGenus`](EllipticWitness.lean) and [`AdelicGenusFact`](FinitePrimes.lean). Genus of the compactified effective modular quotient. |
| `adelic_index` | `curvedata` | Checked with evidence | [`EllipticWitness.adelicIndex`](EllipticWitness.lean) and [`AdelicImageFact`](FinitePrimes.lean). Index in the full integral adelic general linear group. |
| `adelic_level` | `curvedata` | Checked with evidence | [`EllipticWitness.adelicLevel`](EllipticWitness.lean) and [`AdelicImageFact`](FinitePrimes.lean). Least positive modulus with full congruence-kernel containment. |
| `ainvs` | `curvedata` | Checked | [`EllipticWitness.equation`](EllipticWitness.lean) supplies the five coefficients as a Mathlib Weierstrass curve over ℤ. [`EllipticCertificate.nonsingular`](EllipticCertificate.lean) proves its discriminant is nonzero. All checked fields are indexed by that equation. |
| `analytic_rank` | `curvedata` | Checked | [`ConditionalAnalyticRank.correct`](Analytic.lean), stored in [`AnalyticFacts.rank`](Analytic.lean). The catalogue value is compared with the order at 1 for each arithmetic modular realization. The curve evaluators currently certify orders 0 and 1 with full evidence. |
| `bad_primes` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.badPrimes`](FinitePrimes.lean). Complete, duplicate-free list of bad-reduction primes of the globally minimal model. |
| `class_deg` | `curvedata`, `classdata` | Checked | [`IsogenyClassFacts.classDegree`](Algebraic.lean). Maximum of the complete matrix of minimum isogeny degrees. Requires a proved complete class model. |
| `class_size` | `curvedata`, `classdata` | Checked | [`IsogenyClassData.classSize`](Algebraic.lean). Number of distinct rational isomorphism classes, with exhaustive representatives supplied through `with_proofs`. |
| `cm` | `curvedata` | Checked | [`ComplexMultiplicationFacts.endomorphismRing`](Algebraic.lean). The zero code identifies the geometric endomorphism ring with ℤ. A negative code identifies the quadratic order of that discriminant. Requires a geometric ring proof in `with_proofs`. Available at `certificate.complexMultiplication`. |
| `conductor` | `curvedata`, `classdata`, `mwbsd`, `localdata`, `galrep` | Checked | [`ModularArithmeticFacts.conductor`](Invariants.lean). With verified minimality and local data, the value equals the level of each arithmetic modular realization of this curve. This statement concerns the curve supplied to the certifier. |
| `degree` | `curvedata`, `torsion_growth` | Mixed | [`ModularParametrizationInput.degree`](Algebraic.lean) is the reported modular degree in `curvedata`. [`TorsionGrowthFieldFact.degree_eq`](../Support/ExtensionData.lean) checks the absolute degree of the extension in `torsion_growth`. |
| `elladic_images` | `curvedata` | Checked with evidence | [`EllipticWitness.padicImages`](EllipticWitness.lean) and [`PadicImageListFact`](FinitePrimes.lean). Exact listed images with optional non-CM exceptional-prime coverage. |
| `faltings_height` | `curvedata` | Checked | [`PeriodGeometryFacts.height`](Algebraic.lean). Enclosure of `−log(area)/2` on the globally minimal input. |
| `faltings_index` | `curvedata` | Checked | [`FaltingsIndexFact.mem_predecessors`](Algebraic.lean). Counts the exact predecessors in the proved complete isogeny class, with ties ordered by native LMFDB number. |
| `faltings_ratio` | `curvedata` | Checked | [`PeriodGeometryFacts.ratio`](Algebraic.lean). Exact maximum-to-input area ratio for globally minimal representatives of a proved complete rational isogeny class. |
| `intrinsic_torsion` | `curvedata` | Checked | [`IntrinsicTorsionFact.torsion_card`](Algebraic.lean). When rational torsion is proved trivial, every subgroup, including the radical of the rational torsion pairing, has order one. |
| `iso_nlabel` | `curvedata` | Checked | [`LmfdbCatalogueFacts.classIndex`](Algebraic.lean). Zero-based index with a complete ordered conductor roster. |
| `isogeny_degrees` | `curvedata` | Checked | [`IsogenyClassFacts.isogenyDegrees`](Algebraic.lean). Distinct minimum degrees from the input curve, using its row in the proved complete class. |
| `jinv` | `curvedata` | Checked | [`RationalInvariantFacts.jInvariant`](Invariants.lean). Exact equality with the j-invariant after base change to ℚ. |
| `lmfdb_iso` | `curvedata`, `classdata`, `padic` | Checked | [`LmfdbCatalogueFacts.isoLabel`](Algebraic.lean). Class label derived from the actual conductor and ordered roster. Stored p-adic rows use [`StoredPadicRegulatorFact.classLabel_eq`](Analytic.lean) with the independently proved class and reduced model. |
| `lmfdb_label` | `curvedata`, `mwbsd`, `iwasawa`, `torsion_growth`, `localdata`, `galrep` | Checked | [`LmfdbCatalogueFacts.curveLabel`](Algebraic.lean). Curve label derived from both mathematical orderings. Stored p-adic rows use [`StoredPadicRegulatorFact.classLabel_eq`](Analytic.lean) with the independently proved class and reduced model. |
| `lmfdb_number` | `curvedata` | Checked | [`LmfdbCatalogueFacts.number`](Algebraic.lean). One-based position of the reduced minimal equation within its isogeny class. |
| `manin_constant` | `curvedata` | Report | [`ModularParametrizationInput.maninConstant`](Algebraic.lean). Reported differential scaling of the modular parametrization. |
| `min_quad_twist_ainvs` | `curvedata` | Checked | [`MinimumQuadraticTwistFacts.equation`](Algebraic.lean). Requires a globally minimal integral model, a rational change of variables and minimum algorithmic conductor among quadratic twists. Available at `certificate.minimumQuadraticTwist.minimum`. Its optional `uniqueMinimum` evidence proves uniqueness in the ordinary non-CM case. Producer tie-breaking remains open. |
| `min_quad_twist_disc` | `curvedata` | Checked | [`MinimumQuadraticTwistFacts.discriminant`](Algebraic.lean). Fundamental discriminant of the same minimum-conductor twist, at `certificate.minimumQuadraticTwist.minimum.discriminant`. Producer tie-breaking remains open. |
| `modell_images` | `curvedata` | Checked with evidence | [`EllipticWitness.modPrimeImages`](EllipticWitness.lean) and [`ModPrimeImageListFact`](FinitePrimes.lean). Verifies each listed residual conjugacy class, with optional exhaustive non-CM residual support. |
| `modm_images` | `curvedata` | Checked with evidence | [`EllipticWitness.modulusImages`](EllipticWitness.lean) and [`ModulusImageListFact`](FinitePrimes.lean). Verified ordered sublist of the reported finite images, with optional evidence for every submitted entry. |
| `nonmax_primes` | `curvedata` | Checked | [`EllipticWitness.nonmaxPrimes`](EllipticWitness.lean) with [`NonmaxPrimeSupportFact`](FinitePrimes.lean). Proves precisely the exceptional primes for geometrically non-CM curves. |
| `nonmax_rad` | `curvedata` | Checked | [`EllipticWitness.nonmaxRadical`](EllipticWitness.lean) and [`NonmaxPrimeSupportFact.primes`](FinitePrimes.lean). Exact product over the proved support. |
| `num_bad_primes` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.numBadPrimes`](FinitePrimes.lean). Cardinality of the set of prime factors of the absolute minimal discriminant. |
| `num_int_pts` | `curvedata` | Checked | [`CompleteIntegralPointFacts.integralPoints_card`](Algebraic.lean). The count covers every affine integral solution on the supplied model. It requires [`IntegralXSupport.covers`](InputData.lean). |
| `optimality` | `curvedata` | Report | [`ModularParametrizationInput.optimalityCode`](Algebraic.lean). Preserves the producer’s ambiguity codes. |
| `potential_good_reduction` | `curvedata` | Checked | [`ArithmeticFacts.potentialGoodReduction`](FinitePrimes.lean). The Boolean is equivalent to potential good reduction at every rational prime. |
| `rank` | `curvedata` | Checked | [`AlgebraicFacts.rank`](Algebraic.lean). A proved singleton rank interval determines the exact Mordell–Weil rank over ℚ. |
| `regulator` | `curvedata` | Checked | [`RegulatorFacts.within_error`](Algebraic.lean). The structure bounds the error against TauCeti’s regulator. The command currently constructs it for proved rank zero, where the regulator equals one. |
| `semistable` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.semistable`](FinitePrimes.lean). The Boolean characterizes semistable reduction of the rational curve using a checked globally minimal model. |
| `serre_invariants` | `curvedata` | Report | [`GaloisImageClaims.serreInvariants`](FinitePrimes.lean) holds [`SerreInvariantClaim`](FinitePrimes.lean). Each entry gives a prime, weight, and conductor. |
| `sha` | `curvedata` | Checked | [`RoundedAnalyticShaFact.rounds`](Analytic.lean). The enclosure for the analytic BSD quotient singles out the reported nearest integer. Available at `certificate.roundedAnalyticSha`. |
| `sha_primes` | `curvedata` | Checked | [`RoundedAnalyticShaFact.primes`](Analytic.lean). Prime divisors of that rounded integer. Available at `certificate.roundedAnalyticSha`. |
| `signD` | `curvedata` | Checked | [`RationalInvariantFacts.discriminantSign`](Invariants.lean). Sign of the integral equation’s discriminant. |
| `squarefree_disc` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.squarefreeDiscriminant`](FinitePrimes.lean). The Boolean characterizes squarefreeness of the absolute minimal discriminant. |
| `stable_faltings_height` | `curvedata` | Checked | [`PeriodGeometryFacts.stableHeight`](Algebraic.lean). Enclosure for the height plus the logarithmic correction from the j-invariant denominator and discriminant. |
| `szpiro_ratio` | `curvedata` | Checked | [`ModifiedSzpiroRatioFacts.within_error`](Invariants.lean). Enclosure for the modified ratio using the minimal model’s c-invariants and the norm of TauCeti’s algorithmic conductor. Requires arithmetic evidence and an explicit radius. Available at `certificate.modifiedSzpiroRatio`. |
| `torsion` | `curvedata`, `torsion_growth` | Mixed | [`TorsionWitness.cardinality`](Algebraic.lean) is the checked rational torsion order in `curvedata`. [`TorsionGrowthFacts.equivalence`](Algebraic.lean) specifies the full torsion group over the stated extension in `torsion_growth`. |
| `torsion_primes` | `curvedata` | Checked | [`TorsionPrimeSupportFacts.exact_support`](Algebraic.lean). Distinct prime divisors of the verified rational torsion order. |
| `torsion_structure` | `curvedata` | Checked | [`TorsionWitness.presentation`](Algebraic.lean). The verified product of invariant factors is the full subgroup. Each standard generator maps to a specified supplied point. |

## Isogeny class (`ec_classdata`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `anlist` | `classdata` | Checked | [`ArithmeticFacts.dirichletCoefficients`](FinitePrimes.lean). Consecutive coefficients of the rational curve’s L-function, starting at a₁. The JSON decoder checks and removes the initial a₀ = 0. |
| `aplist` | `classdata` | Checked | [`ArithmeticFacts.primeCoefficients`](FinitePrimes.lean). Each supplied prime-indexed coefficient agrees with the represented curve’s L-function. |
| `isogeny_matrix` | `classdata` | Checked | [`IsogenyClassData.isogenyMatrix`](Algebraic.lean). Each entry is attained by an isogeny and bounds every degree from below for that ordered pair. The check requires the canonical LMFDB ordering of reduced minimal models. |
| `trace_hash` | `classdata` | Checked | [`TraceHashFact.correct`](FinitePrimes.lean). Exact weighted residue from a full proof of the curve’s prescribed prime coefficients. |

## Mordell–Weil and BSD data (`ec_mwbsd`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `area` | `mwbsd` | Checked | [`PeriodGeometryFacts.area`](Algebraic.lean). Enclosure of the Euclidean covolume of the complex period lattice for the globally minimal equation. |
| `gens` | `mwbsd` | Checked | [`AlgebraicFacts.generators`](Algebraic.lean) is an indexed family of Mathlib rational points, in input order. Spanning the Mordell–Weil group is a separate assertion. The optional generator-index request checks supplied integer independence at `certificate.algebraic.independentGeneratorPoints`. |
| `heights` | `mwbsd` | Checked | [`CanonicalHeightFacts.within_error`](Algebraic.lean) in `certificate.algebraic.heights`. The enclosures are indexed by the checked `gens` points in order. |
| `ngens` | `mwbsd` | Checked | [`AlgebraicFacts.generators`](Algebraic.lean). Length of the supplied and checked generator list, checked against `ngens` at ingestion. |
| `rank_bounds` | `mwbsd` | Checked | [`EllipticCurve.AlgebraicRankBounds`](Algebraic.lean), stored in [`AlgebraicFacts.rankBounds`](Algebraic.lean). Both endpoints bound Mathlib’s integer-module finrank of the rational points. |
| `real_period` | `mwbsd` | Checked | [`RealPeriodFact.correct`](Analytic.lean). Enclosure for the full minimal real period, including all real components. Available at `certificate.realPeriod`. |
| `sha_an` | `mwbsd` | Checked | [`AnalyticShaFact.correct`](Analytic.lean). Enclosure for the analytic BSD quotient for each arithmetic modular realization. Available at `certificate.analyticSha`. |
| `special_value` | `mwbsd` | Checked | [`SpecialLValueFacts.correct`](Analytic.lean). At proved order $r=0$ or $1$, the reported value differs from the Taylor leading coefficient $L^{(r)}(1)/r!$ by at most the supplied error for each arithmetic modular realization. |
| `tamagawa_product` | `mwbsd` | Checked | [`TamagawaProductFact.correct`](Analytic.lean). Equality with the product of intrinsic Tamagawa factors over finite places. Available at `certificate.tamagawaProduct`. |
| `torsion_generators` | `mwbsd` | Checked | [`TorsionWitness.generators`](Algebraic.lean) holds the submitted points. Exact orders, full generation and invariant-factor generator images use those same indices when proved. |
| `xcoord_integral_points` | `mwbsd` | Checked | [`IntegralYFiberFacts.complete`](Algebraic.lean). Every integral y at each supplied x is accounted for. A proof that the list covers all integral x-values can be supplied as [`IntegralXSupport.covers`](InputData.lean). |

## Local reduction (`ec_localdata`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `conductor_valuation` | `localdata` | Checked | [`ModularArithmeticFacts.conductorValuations`](Invariants.lean). Each supplied prime and exponent is checked against the factorization of the modular realization’s level. |
| `discriminant_valuation` | `localdata` | Checked | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) checks [`LocalReductionClaim.discriminantValuation`](InputData.lean) against the valuation of the absolute minimal discriminant. |
| `j_denominator_valuation` | `localdata` | Checked | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) checks [`LocalReductionClaim.jDenominatorValuation`](InputData.lean) against the valuation of the reduced denominator of j. |
| `kodaira_symbol` | `localdata` | Mixed | [`LocalKodairaFact.correct`](FinitePrimes.lean) checks Iₙ exactly and excludes every Iₙ for an additive code. [`LocalKodairaSymbolFact.correct`](FinitePrimes.lean) specifies the full intrinsic symbol at the supplied prime. |
| `prime` | `localdata`, `galrep` | Mixed | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) proves primality for a checked local row. In `galrep`, [`PrimeGaloisImageClaim.prime`](FinitePrimes.lean) indexes a prime-specific report and [`AdelicGaloisImageClaim`](FinitePrimes.lean) represents the adelic sentinel 0. |
| `reduction_type` | `localdata` | Checked | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) checks [`LocalReductionClaim.reductionType`](InputData.lean). On a bad-prime row the code distinguishes additive (0), split multiplicative (1), and nonsplit multiplicative (−1) reduction and agrees with the Frobenius trace. |
| `root_number` | `localdata` | Exact arithmetic formula | [`LocalReductionClaim.rootNumber`](InputData.lean) and [`LocalRootNumberFact.correct`](FinitePrimes.lean). With checked minimality and finite transcripts, the command exports the local sign through `certificate.arithmetic.minimalModel` in `localRootNumbers`. Comparison with the intrinsic local epsilon factor remains open. |
| `tamagawa_number` | `localdata` | Checked | [`LocalTamagawaFact.correct`](FinitePrimes.lean). The record accepts a proof of any intrinsic local factor. The command currently verifies the value one at good or I₁ reduction. |

## Galois representations (`ec_galrep`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `adelic_gens` | `galrep` | Checked | [`EllipticWitness.adelicGenerators`](EllipticWitness.lean) with [`FiniteGaloisImageFact`](FinitePrimes.lean). The matrices generate the entire image on torsion at the reported modulus. |
| `adelic_image` | `galrep` | Checked with evidence for `N.i.g.?` | [`EllipticWitness.adelicImage`](EllipticWitness.lean) and [`AdelicImageCertificate.partialLabel`](FinitePrimes.lean). Exact level, index and genus with the conjugacy-class suffix unspecified at source prime 0. |
| `elladic_image` | `galrep` | Checked with evidence | [`EllipticWitness.padicImage`](EllipticWitness.lean) and [`PadicImageLabelFact`](FinitePrimes.lean). Full Tate-module image up to conjugacy for a supported native subgroup label. |
| `modell_image` | `galrep` | Checked with evidence | [`EllipticWitness.modPrimeImage`](EllipticWitness.lean) and [`ModPrimeImageFact`](FinitePrimes.lean). Identifies the full residual image up to conjugacy at the source row's prime. |

## p-adic regulators (`ec_padic`)

The native path is conditional on independent sigma evaluation, an integral
Mordell–Weil basis, class order, and a unique reduced minimal model in the
rational isogeny class.

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `p` | `padic` | Checked with evidence | [`StoredPadicRegulatorFact.good`](Analytic.lean) and [`ordinary`](Analytic.lean) prove good ordinary reduction at the reported prime. |
| `prec` | `padic` | Checked with evidence | [`StoredPadicRegulatorFact.contains`](Analytic.lean) proves containment at the submitted absolute precision. |
| `unit` | `padic` | Checked with evidence | [`StoredPadicRegulatorFact.normalized`](Analytic.lean) and [`contains`](Analytic.lean) identify the canonical residue representative. |
| `val` | `padic` | Checked with evidence | [`StoredPadicRegulatorFact.valuation_eq`](../../Verification/PadicRegulator.lean) gives the exact valuation of the nonzero normalized height. |

The curve-level rank-zero display has a separate checked finite-precision encoding.

| Field | Scope | Status | Checked projection |
| --- | --- | --- | --- |
| `p` | Rank-zero display | Checked | [`RankZeroPadicRegulatorFact.good`](Analytic.lean) and [`RankZeroPadicRegulatorFact.ordinary`](Analytic.lean) prove smooth ordinary reduction at the prime in the report. |
| `prec`, `val`, `unit` | Rank-zero display | Checked | [`RankZeroPadicRegulatorFact.contains`](Analytic.lean) proves that the normalized ball contains the curve’s empty height determinant. [`RankZeroPadicRegulatorFact.normalized`](Analytic.lean) bounds the unit representative. |

The fact is available through `certificate.analytic.padicRegulator`.
Proofs use the specified equation and its actual Mordell–Weil rank.
The class label supplies catalogue provenance.

## Torsion growth (`ec_torsion_growth`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `field` | `torsion_growth` | Checked | [`TorsionGrowthFieldFact.polynomial`](Algebraic.lean) in `certificate.torsionGrowthField`. The integral coefficient list presents a field with a torsion point outside the image of rational base change. |

## Iwasawa data (`ec_iwasawa`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `iwdata` | `iwasawa` | Report | [`IwasawaReport.entries`](Analytic.lean) holds [`IwasawaPrimeReport.data`](Analytic.lean). Distinguishes ordinary or multiplicative pairs, signed supersingular data, additive cases, and unknown values. |
| `iwp0` | `iwasawa` | Report | [`IwasawaReport.vanishingThreshold`](Analytic.lean). Optional prime threshold for the reported vanishing at every good prime at or above it. |
