# LMFDB fields and their Lean witnesses

Start with [`EllipticWitness`](EllipticWitness.lean) for input to `certify_ec` and [`EllipticCertificate`](EllipticCertificate.lean) for the checked output, `Name.certificate`. The tables identify each field’s Lean structure and say what evidence it holds. For `ainvs`, the equation itself is the input that indexes the certificate.

The index covers **85 distinct column names** across **101 table-qualified columns** in the eight EC/ℚ tables, excluding the database row identifier `id`. Each name appears once. The table column omits the `ec_` prefix. [LMFDB schema for 37.a1](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)

All 85 names have a Lean record. **Checked** means `certify_ec` can populate the indicated evidence in the stated cases. **Structure** means a record specifies a proof obligation for a future constructor. **Report** records supplied data and may enforce local conditions such as primality. **Metadata** records catalogue provenance. **Mixed** gives the status for each table or case in the row. Command coverage is **46 of 85**. [Certification guide](../../../docs/LMFDB_INVARIANTS.md) · [EC/ℚ roadmap](../../../docs/roadmaps/LMFDB_Q_CERTIFICATION.md)

## Curve data (`ec_curvedata`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `Ciso` | `curvedata` | Metadata | [`CatalogueMetadata.cremonaIso`](InputData.lean). Reported catalogue identifier or ordering. |
| `Clabel` | `curvedata` | Metadata | [`CatalogueMetadata.cremonaLabel`](InputData.lean). Reported catalogue identifier or ordering. |
| `Cnumber` | `curvedata` | Metadata | [`CatalogueMetadata.cremonaNumber`](InputData.lean). Reported catalogue identifier or ordering. |
| `abc_quality` | `curvedata` | Checked | [`AbcQualityFacts.within_error`](Invariants.lean). The reported rational and its error enclose the curve’s abc quality, using a checked factorization with j distinct from 0 and 1728. |
| `absD` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.minimalDiscriminantAbs`](FinitePrimes.lean). Absolute discriminant of a model proved globally minimal. |
| `adelic_genus` | `curvedata` | Report | [`GaloisImageClaims.adelicGenus`](FinitePrimes.lean). Genus reported for the modular curve of the image. |
| `adelic_index` | `curvedata` | Report | [`GaloisImageClaims.adelicIndex`](FinitePrimes.lean). Reported index of the adelic image. |
| `adelic_level` | `curvedata` | Report | [`GaloisImageClaims.adelicLevel`](FinitePrimes.lean). Reported level of the adelic image. |
| `ainvs` | `curvedata` | Checked | [`EllipticWitness.equation`](EllipticWitness.lean) supplies the five coefficients as a Mathlib Weierstrass curve over ℤ. [`EllipticCertificate.nonsingular`](EllipticCertificate.lean) proves its discriminant is nonzero. All checked fields are indexed by that equation. |
| `analytic_rank` | `curvedata` | Checked | [`ConditionalAnalyticRank.correct`](Analytic.lean), stored in [`AnalyticFacts.rank`](Analytic.lean). The catalogue value is compared with the order at 1 for each arithmetic modular realization. The curve evaluators currently certify orders 0 and 1 with full evidence. |
| `bad_primes` | `curvedata` | Checked | [`MinimalModelArithmeticFacts.badPrimes`](FinitePrimes.lean). Complete, duplicate-free list of bad-reduction primes of the globally minimal model. |
| `class_deg` | `curvedata`, `classdata` | Checked | [`IsogenyClassFacts.classDegree`](Algebraic.lean). Maximum of the complete matrix of minimum isogeny degrees. Requires a proved complete class model. |
| `class_size` | `curvedata`, `classdata` | Checked | [`IsogenyClassData.classSize`](Algebraic.lean). Number of distinct rational isomorphism classes, with exhaustive representatives supplied through `with_proofs`. |
| `cm` | `curvedata` | Structure | [`ComplexMultiplicationFacts.endomorphismRing`](Algebraic.lean). The zero code identifies the geometric endomorphism ring with ℤ. A negative code identifies the quadratic order of that discriminant. |
| `conductor` | `curvedata`, `classdata`, `mwbsd`, `localdata`, `galrep` | Checked | [`ModularArithmeticFacts.conductor`](Invariants.lean). With verified minimality and local data, the value equals the level of each arithmetic modular realization of this curve. This statement concerns the curve supplied to the certifier. |
| `degree` | `curvedata`, `torsion_growth` | Mixed | [`ModularParametrizationInput.degree`](Algebraic.lean) is the reported modular degree in `curvedata`. [`TorsionGrowthFieldFact.degree_eq`](../Support/ExtensionData.lean) checks the absolute degree of the extension in `torsion_growth`. |
| `elladic_images` | `curvedata` | Report | [`GaloisImageClaims.padicImages`](FinitePrimes.lean). List of ℓ-adic image labels. |
| `faltings_height` | `curvedata` | Report | [`FaltingsInput.height`](Algebraic.lean). Report in the catalogue’s Faltings-height normalization. |
| `faltings_index` | `curvedata` | Report | [`FaltingsInput.orderingIndex`](Algebraic.lean). Reported position in the isogeny class’s height ordering. |
| `faltings_ratio` | `curvedata` | Report | [`FaltingsInput.ratio`](Algebraic.lean). Reported Néron lattice index relative to the least-height curve in the class. |
| `intrinsic_torsion` | `curvedata` | Report | [`IntrinsicTorsionInput.order`](Algebraic.lean). Reported order of the radical of the rational torsion pairing. |
| `iso_nlabel` | `curvedata` | Metadata | [`CatalogueMetadata.isoNlabel`](InputData.lean). Reported catalogue identifier or ordering. |
| `isogeny_degrees` | `curvedata` | Checked | [`IsogenyClassFacts.isogenyDegrees`](Algebraic.lean). Distinct minimum degrees from the input curve, using its row in the proved complete class. |
| `jinv` | `curvedata` | Checked | [`RationalInvariantFacts.jInvariant`](Invariants.lean). Exact equality with the j-invariant after base change to ℚ. |
| `lmfdb_iso` | `curvedata`, `classdata`, `padic` | Metadata | [`CatalogueMetadata.lmfdbIso`](InputData.lean). Reported catalogue identifier or ordering. |
| `lmfdb_label` | `curvedata`, `mwbsd`, `iwasawa`, `torsion_growth`, `localdata`, `galrep` | Metadata | [`CatalogueMetadata.lmfdbLabel`](InputData.lean). Reported catalogue identifier or ordering. |
| `lmfdb_number` | `curvedata` | Metadata | [`CatalogueMetadata.lmfdbNumber`](InputData.lean). Reported catalogue identifier or ordering. |
| `manin_constant` | `curvedata` | Report | [`ModularParametrizationInput.maninConstant`](Algebraic.lean). Reported differential scaling of the modular parametrization. |
| `min_quad_twist_ainvs` | `curvedata` | Structure | [`MinimumQuadraticTwistFacts.equation`](Algebraic.lean). Requires a rational isomorphism with the proposed twist and minimal algorithmic conductor among quadratic twists. Producer tie-breaking remains open. |
| `min_quad_twist_disc` | `curvedata` | Structure | [`MinimumQuadraticTwistFacts.discriminant`](Algebraic.lean). Fundamental discriminant of the given minimum-conductor twist. Producer tie-breaking remains open. |
| `modell_images` | `curvedata` | Report | [`GaloisImageClaims.modPrimeImages`](FinitePrimes.lean). List of mod-ℓ image labels. |
| `modm_images` | `curvedata` | Report | [`GaloisImageClaims.modmImages`](FinitePrimes.lean). List of image labels at the reported moduli. |
| `nonmax_primes` | `curvedata` | Report | [`GaloisImageClaims.nonmaxPrimes`](FinitePrimes.lean). Exceptional primes under the catalogue’s CM or non-CM convention. |
| `nonmax_rad` | `curvedata` | Report | [`GaloisImageClaims.nonmaxRadical`](FinitePrimes.lean). Reported product of the distinct exceptional primes. |
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
| `stable_faltings_height` | `curvedata` | Report | [`FaltingsInput.stableHeight`](Algebraic.lean). Report in the stable Faltings-height normalization. |
| `szpiro_ratio` | `curvedata` | Structure | [`ModifiedSzpiroRatioFacts.within_error`](Invariants.lean). Enclosure for the modified ratio using the minimal model’s c-invariants and the norm of TauCeti’s algorithmic conductor. |
| `torsion` | `curvedata`, `torsion_growth` | Mixed | [`TorsionFacts.cardinality`](Algebraic.lean) is the checked rational torsion order in `curvedata`. [`TorsionGrowthFacts.equivalence`](Algebraic.lean) specifies the full torsion group over the stated extension in `torsion_growth`. |
| `torsion_primes` | `curvedata` | Checked | [`TorsionPrimeSupportFacts.exact_support`](Algebraic.lean). Distinct prime divisors of the verified rational torsion order. |
| `torsion_structure` | `curvedata` | Checked | [`CyclicTorsionFacts.structure_eq`](Algebraic.lean) or [`TwoFactorTorsionFacts.equivalence`](Algebraic.lean). The proved invariant factors describe the full rational torsion subgroup, including the trivial group. |

## Isogeny class (`ec_classdata`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `anlist` | `classdata` | Checked | [`ArithmeticFacts.dirichletCoefficients`](FinitePrimes.lean). Consecutive coefficients of the rational curve’s L-function, starting at a₁. The JSON decoder checks and removes the initial a₀ = 0. |
| `aplist` | `classdata` | Checked | [`ArithmeticFacts.primeCoefficients`](FinitePrimes.lean). Each supplied prime-indexed coefficient agrees with the represented curve’s L-function. |
| `isogeny_matrix` | `classdata` | Checked | [`IsogenyClassData.isogenyMatrix`](Algebraic.lean). Each entry is attained by an isogeny and bounds every degree from below for that ordered pair. The check requires the canonical LMFDB ordering of reduced minimal models. |
| `trace_hash` | `classdata` | Metadata | [`CatalogueMetadata.traceHash`](InputData.lean). Reported class fingerprint. |

## Mordell–Weil and BSD data (`ec_mwbsd`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `area` | `mwbsd` | Report | [`ComplexPeriodAreaReport.reported`](Analytic.lean). Reported covolume for the Néron differential. |
| `gens` | `mwbsd` | Checked | [`AlgebraicFacts.generators`](Algebraic.lean) holds [`AffineMembership`](InputData.lean). Each decoded rational point lies on the curve. Spanning the Mordell–Weil group is a separate assertion. |
| `heights` | `mwbsd` | Checked | [`CanonicalHeightFacts.within_error`](Algebraic.lean) in `certificate.algebraic.heights`. The enclosures are indexed by the checked `gens` points in order. |
| `ngens` | `mwbsd` | Checked | [`GeneratorCountFacts.length_eq`](Algebraic.lean). Length of the supplied and checked generator list. |
| `rank_bounds` | `mwbsd` | Checked | [`EllipticCurve.AlgebraicRankBounds`](Algebraic.lean), stored in [`AlgebraicFacts.rankBounds`](Algebraic.lean). Both endpoints bound Mathlib’s integer-module finrank of the rational points. |
| `real_period` | `mwbsd` | Checked | [`RealPeriodFact.correct`](Analytic.lean). Enclosure for the full minimal real period, including all real components. Available at `certificate.realPeriod`. |
| `sha_an` | `mwbsd` | Checked | [`AnalyticShaFact.correct`](Analytic.lean). Enclosure for the analytic BSD quotient for each arithmetic modular realization. Available at `certificate.analyticSha`. |
| `special_value` | `mwbsd` | Checked | [`SpecialLValueFacts.correct`](Analytic.lean). At proved order $r=0$ or $1$, the reported value differs from the Taylor leading coefficient $L^{(r)}(1)/r!$ by at most the supplied error for each arithmetic modular realization. |
| `tamagawa_product` | `mwbsd` | Checked | [`TamagawaProductFact.correct`](Analytic.lean). Equality with the product of intrinsic Tamagawa factors over finite places. Available at `certificate.tamagawaProduct`. |
| `torsion_generators` | `mwbsd` | Checked | [`AlgebraicFacts.torsionGenerators`](Algebraic.lean) holds [`AffineMembership`](InputData.lean). The list alone certifies point membership. Exact orders and generation require additional evidence. |
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
| `adelic_gens` | `galrep` | Report | [`AdelicGaloisImageClaim.adelicGenerators`](FinitePrimes.lean). Matrices at a positive modulus. [`FiniteGaloisImageFact`](FinitePrimes.lean) specifies the proof of a finite-level image in a chosen basis. |
| `adelic_image` | `galrep` | Report | [`AdelicGaloisImageClaim.adelicImage`](FinitePrimes.lean). Label for the adelic row (source key 0). |
| `elladic_image` | `galrep` | Report | [`PrimeGaloisImageClaim.padicImage`](FinitePrimes.lean). Reported label. [`PadicGaloisImageFact`](FinitePrimes.lean) specifies the actual Tate-module image in a chosen basis. |
| `modell_image` | `galrep` | Report | [`PrimeGaloisImageClaim.modPrimeImage`](FinitePrimes.lean). Reported label. [`FiniteGaloisImageFact`](FinitePrimes.lean) specifies the finite-level image. |

## p-adic regulators (`ec_padic`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `p` | `padic` | Report | [`PadicRegulatorReport.p`](Analytic.lean). Prime of the reported regulator. |
| `prec` | `padic` | Report | [`PadicRegulatorReport.prec`](Analytic.lean). Absolute precision of the residue. The unit has `prec - val` relative digits. |
| `unit` | `padic` | Report | [`PadicRegulatorReport.unit`](Analytic.lean). Unit representative of the residue, coprime to the reported prime. |
| `val` | `padic` | Report | [`PadicRegulatorReport.val`](Analytic.lean). Signed p-adic valuation of the reported nonzero residue. |

## Torsion growth (`ec_torsion_growth`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `field` | `torsion_growth` | Checked | [`TorsionGrowthFieldFact.polynomial`](Algebraic.lean) in `certificate.torsionGrowthField`. The integral coefficient list presents a field with a torsion point outside the image of rational base change. |

## Iwasawa data (`ec_iwasawa`)

| LMFDB field | Table(s) | Status | Witness and scope |
| --- | --- | --- | --- |
| `iwdata` | `iwasawa` | Report | [`IwasawaReport.entries`](Analytic.lean) holds [`IwasawaPrimeReport.data`](Analytic.lean). Distinguishes ordinary or multiplicative pairs, signed supersingular data, additive cases, and unknown values. |
| `iwp0` | `iwasawa` | Report | [`IwasawaReport.vanishingThreshold`](Analytic.lean). Optional prime threshold for the reported vanishing at every good prime at or above it. |
