# LMFDB fields and their Lean witnesses

Start with [`EllipticWitness`](EllipticWitness.lean) for input to `certify_ec` and [`EllipticCertificate`](EllipticCertificate.lean) for the checked output, `Name.certificate`. Each linked projection below identifies the structure that carries a field’s proof. For `ainvs`, the equation itself is the input that indexes the certificate.

The index covers **85 distinct column names** across **101 table-qualified columns** in the eight EC/ℚ tables displayed by LMFDB on 2026-11-23, excluding the database row identifier `id`. Each name appears once. Table names below omit the `ec_` prefix. A shared name can have a different meaning in another table. [LMFDB schema for 37.a1](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)

**33 names have witness support** in at least one table or case. The descriptions give the precise scope. **52 are to be implemented**, including catalogue metadata for which there is no mathematical witness. For required inputs and example checks, see the [certification guide](../../../docs/LMFDB_INVARIANTS.md). For outstanding mathematical work, see the [EC/ℚ roadmap](../../../docs/roadmaps/LMFDB_Q_CERTIFICATION.md).

## Curve data (`ec_curvedata`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `Ciso` | `curvedata` | **To be implemented.** Cremona isogeny-class label (catalogue metadata). |
| `Clabel` | `curvedata` | **To be implemented.** Cremona curve label (catalogue metadata). |
| `Cnumber` | `curvedata` | **To be implemented.** Curve number in Cremona’s class ordering (catalogue metadata). |
| `abc_quality` | `curvedata` | [`AbcQualityFacts.within_error`](Invariants.lean). The reported rational and its error enclose the curve’s abc quality, using a checked factorization with j distinct from 0 and 1728. |
| `absD` | `curvedata` | [`MinimalModelArithmeticFacts.minimalDiscriminantAbs`](FinitePrimes.lean). Absolute discriminant of a model proved globally minimal. |
| `adelic_genus` | `curvedata` | **To be implemented.** Genus of the modular curve for the adelic image. |
| `adelic_index` | `curvedata` | **To be implemented.** Index of the adelic Galois image. |
| `adelic_level` | `curvedata` | **To be implemented.** Level of the adelic Galois image. |
| `ainvs` | `curvedata` | [`EllipticWitness.equation`](EllipticWitness.lean) supplies the five coefficients as a Mathlib Weierstrass curve over ℤ. [`EllipticCertificate.nonsingular`](EllipticCertificate.lean) proves its discriminant is nonzero. All checked fields are indexed by that equation. |
| `analytic_rank` | `curvedata` | [`ConditionalAnalyticRank.correct`](Analytic.lean), stored in [`AnalyticFacts.rank`](Analytic.lean). The catalogue value is compared with the order at 1 for each arithmetic modular realization. The curve evaluators currently certify orders 0 and 1 with full evidence. |
| `bad_primes` | `curvedata` | [`MinimalModelArithmeticFacts.badPrimes`](FinitePrimes.lean). Complete, duplicate-free list of bad-reduction primes of the globally minimal model. |
| `class_deg` | `curvedata`, `classdata` | **To be implemented.** Largest entry of the complete minimum-isogeny-degree matrix. |
| `class_size` | `curvedata`, `classdata` | **To be implemented.** Number of rational isomorphism classes in the isogeny class. |
| `cm` | `curvedata` | **To be implemented.** CM status and, in the CM case, the discriminant of the geometric endomorphism order. |
| `conductor` | `curvedata`, `classdata`, `mwbsd`, `localdata`, `galrep` | [`ModularArithmeticFacts.conductor`](Invariants.lean). With verified minimality and local data, the value equals the level of each arithmetic modular realization of this curve. This statement concerns the curve supplied to the certifier. |
| `degree` | `curvedata`, `torsion_growth` | **To be implemented.** Modular parametrization degree in `curvedata` and extension-field degree in `torsion_growth` are separate claims. |
| `elladic_images` | `curvedata` | **To be implemented.** List of ℓ-adic Galois images. |
| `faltings_height` | `curvedata` | **To be implemented.** Faltings height. |
| `faltings_index` | `curvedata` | **To be implemented.** Catalogue ordering by Faltings height in the isogeny class. |
| `faltings_ratio` | `curvedata` | **To be implemented.** Index of the least-height curve’s Néron lattice in the given curve’s lattice. |
| `intrinsic_torsion` | `curvedata` | **To be implemented.** Order of the radical of the torsion pairing. |
| `iso_nlabel` | `curvedata` | **To be implemented.** Numerical class label (catalogue metadata). |
| `isogeny_degrees` | `curvedata` | **To be implemented.** Complete list of minimum degrees from this curve. [`DegreeTwoIsogenyFact`](Algebraic.lean) certifies an individual edge. |
| `jinv` | `curvedata` | [`RationalInvariantFacts.jInvariant`](Invariants.lean). Exact equality with the j-invariant after base change to ℚ. |
| `lmfdb_iso` | `curvedata`, `classdata`, `padic` | **To be implemented.** LMFDB class identifier (catalogue metadata). |
| `lmfdb_label` | `curvedata`, `mwbsd`, `iwasawa`, `torsion_growth`, `localdata`, `galrep` | **To be implemented.** LMFDB curve identifier (catalogue metadata). |
| `lmfdb_number` | `curvedata` | **To be implemented.** Curve number within the LMFDB class (catalogue metadata). |
| `manin_constant` | `curvedata` | **To be implemented.** Differential scaling of the modular parametrization. |
| `min_quad_twist_ainvs` | `curvedata` | **To be implemented.** Equation of the minimal quadratic twist with the required minimality comparison. |
| `min_quad_twist_disc` | `curvedata` | **To be implemented.** Discriminant identifying the quadratic twist to the minimal representative. |
| `modell_images` | `curvedata` | **To be implemented.** List of mod-ℓ Galois images. |
| `modm_images` | `curvedata` | **To be implemented.** Mod-m Galois image labels. |
| `nonmax_primes` | `curvedata` | **To be implemented.** Complete list of exceptional primes for the Galois image. |
| `nonmax_rad` | `curvedata` | **To be implemented.** Product of the distinct exceptional primes. |
| `num_bad_primes` | `curvedata` | [`MinimalModelArithmeticFacts.numBadPrimes`](FinitePrimes.lean). Cardinality of the set of prime factors of the absolute minimal discriminant. |
| `num_int_pts` | `curvedata` | [`CompleteIntegralPointFacts.integralPoints_card`](Algebraic.lean). The count covers every affine integral solution on the supplied model. It requires [`IntegralXSupport.covers`](InputData.lean). |
| `optimality` | `curvedata` | **To be implemented.** Optimal modular quotient and the catalogue’s ambiguity codes. |
| `potential_good_reduction` | `curvedata` | [`ArithmeticFacts.potentialGoodReduction`](FinitePrimes.lean). The Boolean is equivalent to potential good reduction at every rational prime. |
| `rank` | `curvedata` | [`AlgebraicFacts.rank`](Algebraic.lean). A proved singleton rank interval determines the exact Mordell–Weil rank over ℚ. |
| `regulator` | `curvedata` | [`RegulatorFacts.within_error`](Algebraic.lean). The structure bounds the error against TauCeti’s regulator. The command currently constructs it for proved rank zero, where the regulator equals one. |
| `semistable` | `curvedata` | [`MinimalModelArithmeticFacts.semistable`](FinitePrimes.lean). The Boolean characterizes semistable reduction of the rational curve using a checked globally minimal model. |
| `serre_invariants` | `curvedata` | **To be implemented.** Exceptional-prime, Serre-weight and Serre-conductor data. |
| `sha` | `curvedata` | **To be implemented.** Catalogue integer derived from the analytic BSD quotient. |
| `sha_primes` | `curvedata` | **To be implemented.** Prime support of the stored integer Sha value. |
| `signD` | `curvedata` | [`RationalInvariantFacts.discriminantSign`](Invariants.lean). Sign of the integral equation’s discriminant. |
| `squarefree_disc` | `curvedata` | [`MinimalModelArithmeticFacts.squarefreeDiscriminant`](FinitePrimes.lean). The Boolean characterizes squarefreeness of the absolute minimal discriminant. |
| `stable_faltings_height` | `curvedata` | **To be implemented.** Stable Faltings height. |
| `szpiro_ratio` | `curvedata` | **To be implemented.** Modified Szpiro ratio of a minimal model. |
| `torsion` | `curvedata`, `torsion_growth` | [`TorsionFacts.cardinality`](Algebraic.lean) proves the order of the full rational torsion subgroup for `curvedata`. The invariant factors after base change in `torsion_growth` are **to be implemented**. |
| `torsion_primes` | `curvedata` | [`TorsionPrimeSupportFacts.exact_support`](Algebraic.lean). Distinct prime divisors of the verified rational torsion order. |
| `torsion_structure` | `curvedata` | [`CyclicTorsionFacts.structure_eq`](Algebraic.lean) or [`TwoFactorTorsionFacts.equivalence`](Algebraic.lean). The proved invariant factors describe the full rational torsion subgroup, including the trivial group. |

## Isogeny class (`ec_classdata`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `anlist` | `classdata` | [`ArithmeticFacts.dirichletCoefficients`](FinitePrimes.lean). Consecutive coefficients of the rational curve’s L-function, starting at a₁. The JSON decoder checks and removes the initial a₀ = 0. |
| `aplist` | `classdata` | [`ArithmeticFacts.primeCoefficients`](FinitePrimes.lean). Each supplied prime-indexed coefficient agrees with the represented curve’s L-function. |
| `isogeny_matrix` | `classdata` | **To be implemented.** Complete matrix of minimum isogeny degrees. [`DegreeTwoIsogenyFact`](Algebraic.lean) certifies one degree-two relation. |
| `trace_hash` | `classdata` | **To be implemented.** Catalogue fingerprint of the trace data. |

## Mordell–Weil and BSD data (`ec_mwbsd`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `area` | `mwbsd` | **To be implemented.** Area of the complex period lattice. |
| `gens` | `mwbsd` | [`AlgebraicFacts.generators`](Algebraic.lean) holds [`AffineMembership`](InputData.lean). Each decoded rational point lies on the curve. Spanning the Mordell–Weil group is a separate assertion. |
| `heights` | `mwbsd` | **To be implemented.** Canonical heights of the listed generators. |
| `ngens` | `mwbsd` | [`GeneratorCountFacts.length_eq`](Algebraic.lean). Length of the supplied and checked generator list. |
| `rank_bounds` | `mwbsd` | [`EllipticCurve.AlgebraicRankBounds`](Algebraic.lean), stored in [`AlgebraicFacts.rankBounds`](Algebraic.lean). Both endpoints bound Mathlib’s integer-module finrank of the rational points. |
| `real_period` | `mwbsd` | **To be implemented.** Full real Néron period. |
| `sha_an` | `mwbsd` | **To be implemented.** Analytic order of Sha from the BSD quotient. |
| `special_value` | `mwbsd` | [`SpecialLValueFacts.correct`](Analytic.lean). At proved order $r=0$ or $1$, the reported value differs from the Taylor leading coefficient $L^{(r)}(1)/r!$ by at most the supplied error for each arithmetic modular realization. |
| `tamagawa_product` | `mwbsd` | **To be implemented.** Product of the intrinsic local Tamagawa factors over all bad primes. |
| `torsion_generators` | `mwbsd` | [`AlgebraicFacts.torsionGenerators`](Algebraic.lean) holds [`AffineMembership`](InputData.lean). The list alone certifies point membership. Exact orders and generation require additional evidence. |
| `xcoord_integral_points` | `mwbsd` | [`IntegralYFiberFacts.complete`](Algebraic.lean). Every integral y at each supplied x is accounted for. A proof that the list covers all integral x-values can be supplied as [`IntegralXSupport.covers`](InputData.lean). |

## Local reduction (`ec_localdata`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `conductor_valuation` | `localdata` | [`ModularArithmeticFacts.conductorValuations`](Invariants.lean). Each supplied prime and exponent is checked against the factorization of the modular realization’s level. |
| `discriminant_valuation` | `localdata` | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) checks [`LocalReductionClaim.discriminantValuation`](InputData.lean) against the valuation of the absolute minimal discriminant. |
| `j_denominator_valuation` | `localdata` | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) checks [`LocalReductionClaim.jDenominatorValuation`](InputData.lean) against the valuation of the reduced denominator of j. |
| `kodaira_symbol` | `localdata` | [`LocalKodairaFact.correct`](FinitePrimes.lean). Good and multiplicative reduction give the exact Iₙ symbol. An additive code excludes every Iₙ. Identifying the specific additive symbol is **to be implemented**. |
| `prime` | `localdata`, `galrep` | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) proves primality for the local row keyed by [`LocalReductionClaim.prime`](InputData.lean). The Galois-image row key in `galrep`, including its adelic sentinel 0, is **to be implemented**. |
| `reduction_type` | `localdata` | [`MinimalModelArithmeticFacts.localRows`](FinitePrimes.lean) checks [`LocalReductionClaim.reductionType`](InputData.lean). On a bad-prime row the code distinguishes additive (0), split multiplicative (1), and nonsplit multiplicative (−1) reduction and agrees with the Frobenius trace. |
| `root_number` | `localdata` | **To be implemented.** Root number at the specified prime. The global sign has its own witness. |
| `tamagawa_number` | `localdata` | [`LocalTamagawaFact.correct`](FinitePrimes.lean). The command proves the intrinsic local factor equals one at good or I₁ reduction. The other reduction cases are **to be implemented**. |

## Galois representations (`ec_galrep`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `adelic_gens` | `galrep` | **To be implemented.** Generators for the adelic Galois image. |
| `adelic_image` | `galrep` | **To be implemented.** Adelic Galois image of this curve. |
| `elladic_image` | `galrep` | **To be implemented.** ℓ-adic Galois image for this row. |
| `modell_image` | `galrep` | **To be implemented.** Mod-ℓ Galois image for this row. |

## p-adic regulators (`ec_padic`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `p` | `padic` | **To be implemented.** Prime of the p-adic regulator. |
| `prec` | `padic` | **To be implemented.** Precision of the p-adic regulator residue. |
| `unit` | `padic` | **To be implemented.** Unit part of the p-adic regulator at the stated precision. |
| `val` | `padic` | **To be implemented.** Valuation of the p-adic regulator. |

## Torsion growth (`ec_torsion_growth`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `field` | `torsion_growth` | **To be implemented.** Defining field for the torsion-growth row. |

## Iwasawa data (`ec_iwasawa`)

| LMFDB field | Table(s) | Witness and scope |
| --- | --- | --- |
| `iwdata` | `iwasawa` | **To be implemented.** Prime-indexed Iwasawa invariants. |
| `iwp0` | `iwasawa` | **To be implemented.** Uniform large-prime vanishing threshold for the Iwasawa invariants. |
