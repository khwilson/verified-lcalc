# LMFDB invariants through `certify_ec`

The [EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md) inventories the related LMFDB tables and specifies the reusable theorem and checker work for the remaining interpretations and cases.

`certify_ec` remains the sole public interface. Each optional witness field
requests a check against the represented curve. Missing fields make no claim.
For a recognized field whose required arithmetic evidence is absent, the command
reports it as unverified and emits no mathematical correctness theorem for it.
Incorrect supplied evidence or a failed supported check rejects the entire
certificate. `claimed_*` definitions and `*_input_eq` bindings record input;
they do not themselves assert that its value is correct.

## What counts as a field

The [field-to-witness index](../VerifiedLcalc/Certificate/Witnesses/README.md) maps each column name to its Lean structure and distinguishes checked evidence, standalone proof obligations, and reported data.

On 2026-11-22 the eight schema tables on the 37.a1 data page displayed **101
table-qualified columns and 85 distinct column names**. This corrects the count
of 84 in the original coverage PR. The count takes each table's displayed
column names once and excludes the database row identifier `id`. An individual
curve's JSON export can omit columns. [LMFDB schemas](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)
· [Original coverage PR](https://github.com/khwilson/verified-lcalc/pull/1)

| Table | Displayed columns | Certificate evidence or roadmap |
| --- | ---: | --- |
| `ec_curvedata` | 51 | The checked curve carries equation, rational, algebraic, arithmetic, analytic and torsion facts. The field table below gives the evidence required for each supported claim. |
| `ec_classdata` | 8 | Checked coefficients concern the represented curve. With proved complete class evidence, the command checks the class size, maximum minimum degree and an ordered degree matrix. |
| `ec_mwbsd` | 13 | Point membership, generator count, rank bounds and integral point fibers are in `certificate.algebraic`. Exhaustive integral-point data requires a proof covering every abscissa. |
| `ec_localdata` | 10 | Checked local arithmetic facts are indexed by prime. Exact Kodaira and Tamagawa outputs depend on the reduction case. |
| `ec_galrep` | 7 | The generator field is checked at the reported finite modulus in a proved torsion basis. Supported residual labels identify exact images up to conjugacy. Partial adelic labels carry exact level, index and genus with a separate simultaneous image proof. |
| `ec_padic` | 5 | The native rank-one singleton-class ball is checked at a good ordinary prime above three with independent sigma evidence. The separate rank-zero display encoding uses the curve-level empty determinant. |
| `ec_torsion_growth` | 4 | A supplied proof checks strict growth and can identify the full torsion group over the presented field. G2 tracks primitive growth. |
| `ec_iwasawa` | 3 | Checked selected prime rows and a universal good-prime vanishing bound, with normalized interpolation evidence. |

The command covers **85 of 85 distinct LMFDB column names** with the evidence
specified below. Assigning each name to one table where its interpretation
has a checker gives 51 in `ec_curvedata`, 4 in `ec_classdata`, 11 in
`ec_mwbsd`, 8 in `ec_localdata`, 4 in `ec_galrep`, 4 in `ec_padic`,
1 in `ec_torsion_growth`, and 2 in `ec_iwasawa`. Shared names such as
`class_size` count once. Counting table-qualified interpretations separately
gives **101 of 101** with a supported check under the corresponding evidence requirements.
The four stored p-adic coordinates enter this tally through the proof-parametric
rank-one checker. The curve-level rank-zero display and project-specific keys
are outside the stored-column count.

## Imported fixture evidence

The [fixture audit](../tests/consumers/FixtureFieldCoverage.lean) tracks
table-qualified examples separately from checker availability. Its denominator
comes from the same [field catalogue](../VerifiedLcalc/Certificate/FieldCatalogue.lean)
and includes all 101 table-qualified columns. The audit verifies that each
listed example names a Lean theorem and checks its axiom dependencies. The
propositions bind the values and their scope to compiled fixture equations.

Run the following after `make test-lmfdb-ci` to print a JSON report.

```sh
VERIFIED_LCALC_FIXTURE_COVERAGE=1 lake -f lakefile.certificates.lean env lean tests/consumers/FixtureFieldCoverage.lean
```

The companion's fixture view includes the Lean statements and their source
locations. The CI comparison regenerates the [JSON index](../web/certificates/fixture-field-coverage.json)
from the compiled fixtures and checks the displayed source links. After
changing a sample, run `python3 scripts/check_fixture_coverage.py --write`
to update the index. The **Refresh certificate companion** workflow deploys the
fixture view alongside existing released curve catalogs and pins the source
links to the deployed commit.

Each `sampled` entry links a curve identifier and theorem name to the
statement verified. The `unconditional` samples use only Lean's standard
axioms, `assumption_backed` samples use the authorized elliptic modularity
axiom, and `conditional_fixture` samples name a theorem with an explicit
mathematical input. Each sample states its source and whether its extent
is partial or complete for the stated case. A partial proof can check a
prefix of a list or a weaker mathematical assertion about the same data.
The squarefreeness example is computed from the equation. A
`pending_review` entry has a checker route and awaits
a curated example in this audit. A `missing_checker` entry has only a report
route. The `report_only_scopes` and `metadata_scopes` lists describe cases that
are outside a checked mathematical claim. A single sampled field can have
multiple kinds of evidence. For example, the 112.a2 example proves analytic
order one with the modularity axiom, while the 37.a1 example is quantified
over an explicit modular realization.

The initial sample set uses the [arithmetic CI fixtures](../tests/fixtures/lmfdb/README.md)
and the [compiled rank fixtures](../tests/consumers/CatalogueAnalyticRank.lean).
For 179.a1 at 179, the audit identifies the intrinsic Tamagawa factor, the
exact Kodaira symbol, and the arithmetic local-sign formula. For 112.a2,
it identifies rational torsion cardinality and cyclic structure, point
membership, a complete integral fiber at one specified abscissa, and
conditional modular-level facts. These scopes matter when using the report
as a checklist for additional curves.

## Scope of checked coverage

Count coverage by the mathematical assertion and the evidence a consumer can
project. For example, `ec_curvedata.torsion` is a cardinality over ℚ, while
`ec_torsion_growth.torsion` gives invariant factors over a specified extension.
The rational cardinality is available through `certificate.torsion.cardinality`.
The extension presentation is available through `certificate.torsionGrowth`
when the caller supplies the full additive equivalence with `with_proofs`.
The row lists factors of order at least two in divisibility order. The empty
list denotes the trivial group, which cannot witness strict growth.

## Arithmetic trace fingerprint

`trace_hash` is checked against the exact weighted sum of the rational L-function
coefficients at all 464 primes in `[4096,8192)`, reduced modulo `2^61 - 1`.
`TraceHashCoefficients.correct` supplies the exact list equality. The aggregate
`certificate.traceHash` retains the vector and the equality for the actual curve.
A matching residue alone gives no identification of a class.
[LMFDB trace-hash producer](https://github.com/LMFDB/lmfdb/blob/28f9f0e38f2f027b13edcb2facece1bb45b47170/lmfdb/utils/trace_hash.py)

## Cremona singleton orderings

In the published conductor range up to 500000, `Cnumber` can be checked
with an exhaustive presentation of a one-isomorphism-type isogeny class.
`Ciso` needs an exhaustive roster of one rational isogeny class at the
actual conductor. `Clabel` requires both proofs. The matching suffixes are
`1`, `a`, and `a1`, respectively. The typed evidence and projections are
available through `certificate.cremonaCatalogue`.
[LMFDB Cremona labels](https://www.lmfdb.org/knowledge/show/ec.q.cremona_label)
· [Published Cremona tables](https://github.com/JohnCremona/ecdata/tree/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allcurves)

## Mathematical catalogue ordering

| LMFDB field | Checked projection in `certificate.lmfdbCatalogue` | Evidence |
| --- | --- | --- |
| `lmfdb_number` | `number` | Complete rational isogeny class and lexicographic order of its reduced minimal equations. This gives a one-based position. |
| `iso_nlabel` | `classIndex` | Complete rational isogeny class roster at the actual algorithmic conductor, ordered by arithmetic q-expansion. The subject is proved isogenous to the representative at its zero-based position. |
| `lmfdb_iso` | `isoLabel` | The conductor roster gives the conductor and class index used to form the class label. |
| `lmfdb_label` | `curveLabel` | Both proofs give the conductor, class index, and curve number used to form the full label. |

The same field can provide metadata in other tables. The mathematical projection
is scoped to the proved subject equation or its isogeny class. Comparisons use the
reviewed LMFDB ordering and base-26 encoding.
[LMFDB label convention](https://www.lmfdb.org/knowledge/show/ec.q.lmfdb_label)

## Checks implemented

| JSON data | Lean witness field | Mathematical output / required evidence |
| --- | --- | --- |
| `heights` | `canonicalHeights` | `certificate.algebraic.heights` bounds the actual canonical heights of the ordered `gens` points using supplied Lean enclosures. |
| `torsion_growth.field`, `torsion_growth.degree` | `torsionGrowthField` | `certificate.torsionGrowthField` gives an irreducible polynomial, absolute degree, and a new torsion point over that field for this curve. |
| `torsion_growth.torsion` | `torsionGrowthFactors` | `certificate.torsionGrowth` links the exact factor list and defining polynomial to an additive equivalence onto the full torsion subgroup. Supply `IntegralCurveProofs.torsionGrowth` through `with_proofs`. |
| `ainvs` | `equation` | Actual Mathlib `WeierstrassCurve ℤ`; nonsingularity is checked. |
| `binvs`, `cinvs` | `bInvariants`, `cInvariants` | Equalities with Mathlib's b₂,b₄,b₆,b₈ and c₄,c₆. These are optional equation-data extensions. |
| `discriminant` | `discriminant` | Equality with this supplied equation's Mathlib Δ; does not assert minimality. |
| `abc_quality` with `abc_quality_evidence` | `abcQuality` | Proved absolute error bound between the reported decimal and TauCeti’s real abc quality, using the factorization in the evidence. |
| `cm` | `complexMultiplication` | Geometric endomorphism ring identification supplied through `with_proofs`. |
| `min_quad_twist_ainvs` | `minimumTwistEquation` | Globally minimal integral equation of a quadratic twist with the minimum algorithmic conductor. |
| `min_quad_twist_disc` | `minimumTwistDiscriminant` | Fundamental discriminant identifying the same twist, with 1 for the trivial twist. |
| `szpiro_ratio` with `szpiro_ratio_evidence` | `modifiedSzpiroRatio` | Directed-log enclosure using the checked minimal equation and TauCeti’s algorithmic conductor norm. |
| `regulator` with optional `regulator_evidence.error` | `regulator` | With a proved algebraic rank of zero, checks the exact rank-zero regulator value `1` against the reported decimal and explicit error. A report without an error is treated as exact; other ranks remain unverified. |
| `special_value` with `special_value_evidence.error` | `specialLValue` | Checks the reported arithmetic Taylor leading coefficient against the actual central-value enclosure at order zero or first-derivative enclosure at order one, with explicit nonnegative rational error. Higher orders remain unverified. |
| `jinv` | `jInvariant` | Equality with Mathlib's actual rational-curve `j`. Accepts an exact numerator/positive-denominator pair, fraction string, or integer. |
| `j_integral` | `jIntegral` | Exact JSON boolean. The exported `j_integral` theorem equates `IsLocalization.IsInteger ℤ` of Mathlib's j-invariant with the supplied flag being true. |
| `potential_good_reduction` | `potentialGoodReduction` | Exact JSON boolean. The exported theorem equates potential good reduction at every rational prime with the supplied flag being true. |
| `signD` | `discriminantSign` | Equality with the sign of the equation's Δ. |
| `absD` | `minimalDiscriminantAbs` | Actual TauCeti `IsGlobalMinimal` together with the claimed absolute discriminant; requires checked `minimality`. |
| `bad_primes` | `badPrimes` | Complete, duplicate-free prime-divisor list of the minimal discriminant, and equivalence with non-elliptic finite-field reduction; requires `minimality`. |
| `num_bad_primes` | `numBadPrimes` | Cardinality of Mathlib's prime-factor set of the minimal discriminant; requires `minimality`. |
| `semistable` | `semistable` | Equivalence with TauCeti's `WeierstrassCurve.IsSemistable` over the ring of integers of ℚ, using the checked `minimality`. |
| `squarefree_disc` | `squarefreeDiscriminant` | Equivalence with Mathlib's `Squarefree` on the absolute minimal discriminant, using the checked `minimality`. |
| `local_invariants` or a top-level local row | `localInvariants` | Checks each supplied prime and any supplied `discriminant_valuation`, `j_denominator_valuation` or `reduction_type` against the minimal equation, using the checked `minimality`. |
| `tamagawa_number` | `localInvariants` row field `tamagawaNumber` | Exact intrinsic Tamagawa number at good reduction or multiplicative `I₁` or `I₂`. Higher odd-prime multiplicative indices require splitting evidence. Tame II/III/IV require checked terminal evidence. A local test proves minimality at that prime. |
| `tamagawa_splitting` (evidence extension) | `localInvariants` row field `tamagawaSplitting` | At odd-prime multiplicative `Iₙ`, `n ≥ 3`, supplies either a root of the original node polynomial or an Euler-power witness that its discriminant is nonsquare. The verifier checks the value without root search. |
| `kodaira_symbol` | `localInvariants` row field `kodairaSymbol` | Canonical TauCeti `Iₙ` equality for good or multiplicative reduction. For additive codes the theorem excludes every `Iₙ`. Requires `minimality`. |
| `root_number` | `localInvariants` row field `rootNumber` | Arithmetic local sign at the row's prime. Requires checked `minimality` and `local_data`. |
| `ap` / `aplist` | `primeCoefficients` | Actual `LFunction p` coefficients with proved sufficient local minimality checks. |
| `anlist` | `dirichletCoefficients` | Actual consecutive `LFunction n` coefficients; requires `minimality`. Native JSON starts with a₀=0, which is checked and removed; direct Lean lists start at a₁. |
| `conductor` | `conductor` | Identification with the chosen modular realization's level; requires `minimality`, `localData`, and the existing modularity/arithmetic-compatibility axiom. |
| Local `conductor_valuation` | `localInvariants[].conductorValuation` | Proves primality and the claimed exponent in the Mathlib factorization of the curve's checked modular level. Requires a checked `conductor` with `minimality` and `localData`. |
| `global_root_number` | `rootNumber` | Identification with that realization's global root/Fricke sign under the same conditions. This is an explicit extension key, not the local-table `root_number`. |
| `integral_points` | `integralCoordinates` | Point membership on the supplied equation. |
| `xcoord_integral_points` | `integralFiberRoots` | Complete finite y-fibers at the listed x-values, with a double root represented once. The theorem makes no claim over other x-values. |
| `class_size` | `classSize` | Exact number of distinct rational isomorphism classes, given a proved complete class model in `with_proofs`. |
| `class_deg` | `classDegree` | Maximum minimum isogeny degree, computed from the entire proved class matrix. |
| `isogeny_degrees` | `isogenyDegrees` | Duplicate-free list of minimum degrees from the input curve to all class representatives, checked as a set. |
| `isogeny_matrix` | `isogenyMatrix` | Square array of minimum degrees with source indexing rows and target indexing columns. Requires reduced minimal representatives in the LMFDB lexicographic coefficient ordering. |
| `nonmax_primes` | `nonmaxPrimes` | Complete exceptional support of the integral ℓ-adic images of a geometrically non-CM curve. Requires a `NonmaxPrimeSupportFact` through `with_proofs`. |
| `nonmax_rad` | `nonmaxRadical` | Exact product of the distinct primes in the proved complete support. Requires the same evidence and may be submitted independently. |
| `modell_image` | `modPrimeImage` | Exact conjugacy class of the image on all geometric ℓ-torsion, for the reported prime and a supported Sutherland label. |
| `modell_images` | `modPrimeImages` | Exact residual conjugacy classes at the listed entries. Complete non-CM residual support requires separate all-prime evidence. |
| `adelic_level` | `adelicLevel` | Least positive modulus with full kernel containment in the exact simultaneous adelic image. |
| `adelic_index` | `adelicIndex` | Index of that image in the integral adelic general linear group. |
| `adelic_genus` | `adelicGenus` | Genus of the compactified effective quotient of the determinant-one integral pullback. |
| `adelic_image` | `adelicImage` | At prime zero, a partial label `N.i.g.?` is checked against the proved level, index and genus with the class suffix unspecified. |
| `elladic_image` | `padicImage` | Exact integral Tate-module image conjugate to the inverse image of a supported Rouse–Sutherland–Zureick-Brown subgroup at the native row's prime. |
| `elladic_images` | `padicImages` | Exact integral Tate-module image for each submitted label. Exhaustiveness uses independent non-CM support evidence. |
| `modm_images` | `modulusImages` | Checked sublist of native finite-image labels. An incomplete label `N.i.g.?` can certify minimal level, index and genus for the inverse image of the exact mod-`N` group. |
| `serre_invariants` | `serreInvariants` | Complete list of exceptional triples from Serre's published formula on a checked globally minimal semistable equation with good reduction at two. The default conductor is the norm of the algorithmic conductor. The intrinsic residual-ramification comparison is an upstream target. |
| `adelic_gens` | `adelicGenerators` | Complete image on the full geometric torsion of the reported modulus in a supplied basis. Requires an `FiniteGaloisImageFact` through `with_proofs`. |
| `num_int_pts` | `numIntegralPoints` | Exact cardinality theorem from supplied exhaustive `IntegralXSupport`; available at `certificate.algebraic.completeIntegralPoints` with finite-set completeness and `Finite` evidence. Without support it is unverified, but a count below the number of distinct checked points or seed-fiber solutions is rejected. |
| `gens`, `torsion_generators` | `generatorCoordinates`, `torsionGeneratorCoordinates` | Exact weighted triples decode to rational points with checked membership. |
| `rank`, `rank_bounds` | `algebraicRank`, `algebraicRankBounds` | Verify supplied endpoints against a typed proof of bounds on the actual Mordell–Weil rank. A singleton proof gives exact rank. |
| `area` | `area` | Rational enclosure of the Euclidean covolume in ℂ of the globally minimal equation's normalized period lattice. |
| `faltings_height` | `faltingsHeight` | Rational enclosure of `−log(area)/2` on the globally minimal equation. |
| `stable_faltings_height` | `stableFaltingsHeight` | Rational enclosure of the Faltings height plus `log(denominator(j)/abs(Δ))/12`. |
| `faltings_index` | `faltingsIndex` | Exact number of class members preceding the input in increasing Faltings height, with ties ordered by native LMFDB number. Requires exact comparisons on a proved complete and canonically ordered class. |
| `intrinsic_torsion` | `intrinsicTorsion` | Order one for every subgroup of the proved trivial rational torsion group. In particular this proves the order of the radical of the catalogue's torsion pairing. |
| `faltings_ratio` | `faltingsRatio` | Exact positive integer quotient of the greatest area of a globally minimal representative in the proved complete rational isogeny class by the input area. |
| `real_period` | `realPeriod` | A supplied `RealPeriodFact` at `certificate.realPeriod` bounds the full minimal real period, including both real components when present. |
| `tamagawa_product` | `tamagawaProduct` | A supplied `TamagawaProductFact` at `certificate.tamagawaProduct` proves the exact intrinsic product over all rational finite places. |
| `sha_an` | `analyticSha` | A supplied or composed `AnalyticShaFact` at `certificate.analyticSha` encloses the analytic BSD quotient for an explicit modular realization, with exact analytic order and positive denominator. |
| `sha`, `sha_primes` | `sha`, `shaPrimes` | `certificate.roundedAnalyticSha` checks that the quotient enclosure is strictly inside the positive integer's rounding cell and that any listed primes are distinct and exactly its prime support. |
| `ngens` | `generatorCount` | Length of the checked `gens` list. A basis or spanning claim needs its own evidence. |
| `torsion_generator_orders` | `torsionGeneratorOrders` | Project-specific raw order list. The checked torsion family gives the positive exact order at each coordinate index. |
| `torsion_structure` | `torsionStructure` | An additive equivalence onto the full rational torsion subgroup, for cyclic factors or two factors `[2, n]` with verified independence and a matching divisor. |
| `torsion_primes` | `torsionPrimes` | Ascending distinct prime support of the exact full rational torsion cardinality; checked only after that cardinality is proved. |
| `infinite_order_points`, `independent_points` | `infiniteOrderPoints`, `independentPoints` | Integral-coordinate indices for the infinite-order checker or the supplied independence proof. |
| `independent_generator_points` | `independentGeneratorPoints` | Rational generator indices for the supplied independence proof. |
| `torsion_bound` | `torsionBound` | Two odd good-reduction primes and the claimed positive gcd of their finite point counts. The full rational torsion order divides that gcd. |
| `torsion` | `torsion` | Claimed exact order. A gcd of one proves the exact cardinality. For a larger checked bound the claimed order must be positive and divide the bound. |
| Complete numerical payload | `centralResult`, `derivativeResult` | Existing analytic-rank-zero/one certificates under the documented modularity assumption. |

For `nonmax_primes`, the completeness proof covers every prime and identifies
the actual integral Tate-module image in a supplied basis at each prime.
For geometrically non-CM curves, maximality means equality with the full
`GL₂(ℤ_ℓ)`. The CM convention uses a different maximal subgroup.
For example, 338.e1 lists 2 and 7 in `nonmax_primes`, and its residual
`modell_images` lists only a label at 7.
[LMFDB ℓ-adic search](https://github.com/LMFDB/lmfdb/blob/a0c7fdc3b7ab1d7f11d324242e4707896c5b3529/lmfdb/elliptic_curves/elliptic_curve.py#L1344-L1353)
· [LMFDB 338.e1](https://www.lmfdb.org/api/ec_curvedata/1373)

The supported residual labels are `2Cs`, `2B`, `2Cn`, `2G` and
`7B.2.3`. Pointwise comparison applies to CM and non-CM curves. The
optional coverage proof uses full `GL₂(𝔽_ℓ)` as the maximal residual image
for geometrically non-CM curves. CM reporting has a different convention
for what counts as exceptional. Verification accepts each listed label only
with exact subgroup evidence, and a bare empty list gives no coverage proof.
[Sutherland, Section 6.4 and Table 3](https://doi.org/10.1017/fms.2015.33)
· [LMFDB 40.a2](https://www.lmfdb.org/EllipticCurve/Q/40a1/)
· [LMFDB CM example 32.a2](https://www.lmfdb.org/EllipticCurve/Q/data/32.a2)

The `elladic_image` and `elladic_images` labels follow the numeric
Rouse–Sutherland–Zureick-Brown convention. Supported labels have a reference
finite subgroup, and the proof compares the entire integral Tate-module
image with its full inverse image. CM rows may use this pointwise comparison.
Full support requires a separate non-CM premise and all-prime image proof.
[RSZB labels and convention](https://doi.org/10.1017/fms.2022.38)
· [2-adic representatives](https://github.com/AndrewVSutherland/ell-adic-galois-images/blob/66b7084148a4da13b49e0daaa76d88d64d9e085f/groups/gl2_2adic.txt)
· [5-adic representatives](https://github.com/AndrewVSutherland/ell-adic-galois-images/blob/66b7084148a4da13b49e0daaa76d88d64d9e085f/groups/gl2_5adic.txt)
· [LMFDB 69.a1](https://www.lmfdb.org/EllipticCurve/Q/data/69.a1)

The `modm_images` list uses modular-curve labels. The known level-two
representatives are `2.3.0.a.1` and `2.6.0.a.1`. The catalogue also includes
`22.2.0.a.1` from the finite image recorded for 64064.o1. For `N.i.g.?`, Lean checks
the level, index and topological genus of the full inverse image of the
verified finite subgroup. Checking every submitted entry leaves open which
reductions the producer chose to enumerate.
[LMFDB 40.a2](https://www.lmfdb.org/EllipticCurve/Q/40a1/)
· [LMFDB 37.a1](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)
· [LMFDB 64064.o1](https://www.lmfdb.org/EllipticCurve/Q/64064/o/1)

The 37.a1 native row reports `74.2.0.?`. The level and index concern the
unsymmetrized adelic image. Genus uses the effective `PSL₂(ℝ)` image of the
`SL₂(ℤ)` pullback, so the two signs have the same action on the upper
half-plane. The actual compactified quotient supplies cusp and elliptic geometry.
The fixture checks these values conditional on independent all-prime,
kernel, coset and Euler-characteristic evidence.
[LMFDB definitions](https://www.lmfdb.org/knowledge/show/ec.galois_rep_adelic_image)
· [LMFDB 37.a1 source rows](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1)
· [Rouse–Sutherland–Zureick-Brown](https://doi.org/10.1017/fms.2022.38)

For `adelic_gens`, join the prime-zero row to the curve equation. JSON takes the
modulus from `adelic_level` or the first component of `adelic_image` and checks
agreement if both are present. The matrix `[[a,b],[c,d]]` has raw encoding
`[a,b,c,d]` with entries in the range from zero to modulus minus one.
The checked fact in `certificate.adelicGenerators` identifies the subgroup
generated by these matrices with the actual action on all torsion at that
modulus, with columns giving the images of basis vectors. Zywina's
`FindOpenImage` returns matrices for the torsion representation itself.
Minimality of the adelic level and the full profinite image require separate
proofs.
[LMFDB row renderer](https://github.com/LMFDB/lmfdb/blob/a0c7fdc3b7ab1d7f11d324242e4707896c5b3529/lmfdb/elliptic_curves/web_ec.py#L428-L437)
· [LMFDB computation export](https://github.com/LMFDB/lmfdb/blob/a0c7fdc3b7ab1d7f11d324242e4707896c5b3529/lmfdb/elliptic_curves/code.yaml)
· [LMFDB adelic level](https://www.lmfdb.org/knowledge/show/ec.galois_rep_adelic_image)
· [Zywina's image convention](https://github.com/davidzywina/OpenImage/blob/master/main/FindOpenImage.m#L1428-L1439)

`abc_quality` is stored as a double-precision approximation. With explicit
evidence, JSON digits are interpreted as an exact rational center. Supply
`abc_quality_evidence` with a nonnegative exact rational `error` and the
complete list `factors` of prime factors of the reduced abc product, repeated
with multiplicity. The checker proves
`|curve.abcQuality h - reported| ≤ error` using exact dyadic log bounds.
It rejects evidence at j = 0 or 1728, where the quality is undefined.
The logarithms are enclosed at 64 bits. A tighter error request can fail
when those enclosures cannot establish it. A bare decimal remains metadata.
Direct Lean input uses `AbcQualityClaim`.
[LMFDB definition](https://www.lmfdb.org/knowledge/show/ec.q.abc_quality)

Regulator reports accept an exact JSON decimal, canonical decimal string, or Sage `__RealLiteral__`
encoding. The real literal's `data` string is interpreted exactly and its
`prec` field is representation metadata only. An optional
`regulator_evidence.error` supplies a nonnegative exact absolute error as a
JSON decimal, decimal string, fraction string, or numerator/denominator pair; a
binary float or precision tag never creates an error bound. An exact algebraic
rank proof is required before the command exports
`certificate.algebraic.regulator`. At rank zero TauCeti proves the regulator is
exactly one, which is checked against the submitted enclosure. A disjoint
enclosure or negative error rejects the certificate. Missing or partial rank
proofs leave the regulator unverified.
The rank-zero convention reuses TauCeti's
[`regulator_eq_one_of_finrank_eq_zero`](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/Regulator/Basic.lean#L109).

`j_integral` checks whether the j-invariant is the image of an integer.
`potential_good_reduction` uses the same denominator computation to check
potential good reduction over the p-adic integers at every rational prime.
Both checks work without a supplied `jinv` value or minimality evidence.
The geometric theorem follows from TauCeti's local integral j-invariant
criterion and its rational denominator criterion.
[Local criterion](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/PotentialGoodReduction.lean#L438-L442)
· [Denominator criterion](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/NumberTheory/Padics/RatCast.lean#L67-L80)

Equation invariants, minimality, bad-prime, coefficient, semistability, and potential good reduction
results use standard Lean axioms. The local discriminant and j-denominator valuations and reduction codes have the same
dependencies. The `conductor_valuation` theorem uses the authorized modularity assumption through
the checked level equation, as does the conductor certificate. The finite check of the supplied
integer level is independent of that assumption. A comparison with the intrinsic Artin exponent
or with the norm of TauCeti's algorithmic conductor ideal requires a separate theorem.
[Algorithmic conductor ideal](https://github.com/TauCetiProject/TauCeti/pull/15468)

Supplying `minimality` also exports `global_minimal`.
None of these checks certifies an external label or database provenance.

The `num_int_pts` and `xcoord_integral_points` field names are taken from the
current LMFDB [`ec_curvedata` API](https://www.lmfdb.org/api/ec_curvedata/) and
[`ec_mwbsd` API](https://www.lmfdb.org/api/ec_mwbsd/), respectively. The latter
lists `xcoord_integral_points` as a numeric array. These values are inputs; the
Lean support proof, not a database completeness claim, justifies an exact count.

A local row requires `prime`. An optional valuation gives its exponent in the absolute minimal
discriminant, the reduced rational denominator of `j`, or the checked modular level. Conductor
exponents may be supplied for any rational prime and are zero when that prime does not divide the
level. The reduction codes are 0 for additive, 1 for split multiplicative, and −1 for nonsplit
multiplicative reduction. Certificates cover each supplied row individually.

`tamagawa_number` verifies one at good or `I₁` reduction and two at `I₂`
reduction. Both splitting cases at `I₂` have local index two. At an odd prime,
multiplicative `Iₙ` for `n ≥ 3` requires the optional `tamagawa_splitting`
extension in that row: `{"root": x}` checks an explicit root of the original
model's node polynomial, and `{"nonsplit_euler_power": p-1}` checks Euler's
criterion for the nonsquare node discriminant. The verifier never searches
for a root. It proves factor `n` for split reduction and `gcd(2,n)` for
nonsplit reduction. Higher indices at `p = 2` remain unsupported. For a rational prime p > 3, a
`tamagawa_type_iii` object in the same local row supplies the exact integers
`r`, `s`, and `t` of a change of variables with scale 1. The producer proposes
these coordinates. The checker applies the submitted change to the original
equation, tests the terminal III divisibilities, and checks the claimed factor
two. A submitted change that fails its tests is rejected. Rows without the
change can use the good, I₁, and I₂ routes.

Tame type II at a rational prime p > 3 takes `tamagawa_type_ii` with
the exact scale-one change. The checker tests all five terminal conditions
on the changed equation, including the failure of p² divisibility for
the new a₆. Successful evidence gives intrinsic factor one.

Tame type IV at a rational prime p > 3 takes `tamagawa_type_iv` with
the same exact change and one residue evidence key. The checker derives
the terminal quadratic from the changed equation. A supplied `residue_root`
must vanish in that quadratic, giving factor three. A supplied
`nonsplit_euler_power` must equal p−1 and agree with the checked Euler
power of the discriminant modulo p, giving factor one. The producer
can search for a root when proposing evidence. The verifier checks
only the supplied branch.

The equality concerns TauCeti's
`tamagawaNumberAt` over the completed field. The checker needs no global
minimality witness for this field. A claim outside this scope is reported
as unverified. [Completed Tamagawa factor](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Tamagawa/Product.lean#L47-L87)

The producer stores Sage's PARI Kodaira codes. Code 1 represents good
reduction `I₀`. For positive `n`, code `n + 4` represents `Iₙ`.
The `kodaira_symbols` theorem gives the exact symbol for these codes.
For an additive code it proves that the symbol is outside the entire
`Iₙ` family and reports that the exact code remains unverified. Claims that contradict the checked family or multiplicative
index are rejected. A specific additive symbol needs further terminal
Tate-algorithm evidence.
[Producer](https://github.com/JohnCremona/ecdata/blob/25cec5ecfec8b9f016eb1631ac633194c2bed39f/scripts/files.py#L137-L149)
· [PARI code mapping](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/schemes/elliptic_curves/kodaira_symbol.py#L111-L148)

Local claims can be split across rows. When two rows name the same prime,
any supplied single-valued invariants must agree.

`root_number` in an `ec_localdata` row is **local**, at that row's `prime`.
A supplied claim requires a prime and a sign of ±1. With checked `minimality`
and `local_data`, the command verifies the arithmetic formula, including the
wild transcript when additive reduction at 2 or 3 requires one. For curves
requiring no wild transcripts, supply `"local_data":{"at_two":null,"at_three":null}`.
The sign and its proof are available through `local_root_numbers` and
`Name.certificate.arithmetic.minimalModel` in `localRootNumbers`.
Intrinsic local epsilon-factor compatibility still requires a separate theorem.
Use the separate `global_root_number` key for the global sign.

`torsion_bound` takes an object with exact integer fields `first_prime`,
`second_prime`, and `bound`. JSON primes are capped at 10000. The checker
verifies odd primality and good reduction of the supplied equation at both
primes, then recomputes the gcd. The resulting `torsion_bound` theorem proves
divisibility and positivity for the bound. A bound of one also exports
`torsion`, the exact cardinality theorem for the group's trivial case.
A larger bound alone proves divisibility. When the submitted points also give
a cyclic or two-factor subgroup attaining that bound, the certificate proves
the exact cardinality and the claimed structure. A raw `torsion` value alone
supplies neither piece of evidence.

Import `CertifiedCurves.Invariants` for the small reusable 37.a1 example.
`tests/consumers/CertifiedECInvariantsConsumer.lean` imports its `.olean` theorems
without rerunning the certification command.

The four class fields are optional exact claims. Supply
`IntegralCurveProofs.isogenyClass` via `with_proofs` to give the
distinct and exhaustive representatives, the correspondence with the input
curve, and attainment and lower bounds for each matrix entry. The complete
class and any native ordering proof are accessible through
`certificate.isogenyClass`. The checker computes the class degree and the
selected row's degree set. It compares a submitted matrix only with a
proved LMFDB ordering. An edge alone leaves the class fields unverified.
[LMFDB label ordering](https://www.lmfdb.org/knowledge/show/ec.q.lmfdb_label)

## Rational point families and torsion

The optional fields of `certificate.torsion` share the same submitted generator
indices. Decoded coordinates give a native indexed family of rational points.
Positive exact orders prove torsion membership at each supplied index. With a
checked matching cyclic or two-factor presentation, `torsion.generation`
identifies the subgroup generated by the supplied family with all rational
torsion. The `torsion.presentation` identifies that full subgroup with a
product of cyclic factors. Its `indices` map tells which submitted point is
the image of each standard factor generator. An empty factor list represents
the trivial group. A submitted family may also contain extra points when the
checked factor generators can be identified within it.

An optional `ngens` is compared with the size of the checked rational generator
family. The certificate derives the count from that family.

## Real period, Tamagawa product, and analytic quotient

Submit the Lean proof records using `with_proofs`. JSON decimal reports are
parsed exactly and any explicit `real_period_evidence.error` or
`sha_an_evidence.error` must match the radius proved in the attachment.
If the raw radius is omitted, the certificate retains the attached radius.
An attached quotient also checks any submitted `analytic_rank` against its
proved order. Missing attachments leave the corresponding catalogue rows
unverified. `AnalyticShaFact.ofFactors` composes a proved leading coefficient
and exact torsion cardinality with period, regulator, and Tamagawa evidence
using rational interval arithmetic and a strictly positive denominator lower
endpoint. Rounding rejects intervals touching a half-integer boundary. The
checked integer and prime support concern the analytic quotient.

### Modular parametrization data

Supply `IntegralCurveProofs.modularParametrization` with a rational
function-field pullback from the level of the curve's conductor, taking the
cusp at infinity to the identity. The source field uses the rational Laurent
coefficients at the width-one cusp of the compactified effective
Γ₀ quotient. The modular degree must equal the actual extension degree and
be minimal among all positive finite degrees to the same target. On a
globally minimal equation, the Manin constant is the positive scaling of
the Néron differential against the weight-two cusp form whose entire
Fourier expansion matches the arithmetic L-function.

The optional optimality proof compares the full integral image of the
source periods with the Néron period lattice. Equality checks code 1, and
proper inclusion checks code 0. This is the analytic period criterion for
connected kernel of the induced Jacobian quotient. The certificate
exports the lattice equality or proper inclusion. The comparison to an
algebraic Jacobian morphism is a separate upstream target. Codes above
one remain reports about the producer's ambiguous candidate set.
ecdata's reported Manin numbers can depend on a choice of optimal
representative. A successful check independently proves the scaling of
the supplied curve's minimum modular map.

Submit these fields in exact JSON as `degree`, `manin_constant` and
`optimality`, or in Lean via `modularDegree`, `maninConstant` and
`optimality`. The certificate's `modularParametrization` record retains
the supplied geometric evidence and an exact match for each submitted
field that the verifier could check. The modular degree here is distinct
from the extension degree in a torsion-growth row.
[ecdata producer](https://github.com/JohnCremona/ecdata/blob/master/scripts/files.py)
· [LMFDB 11.a2](https://www.lmfdb.org/EllipticCurve/Q/11/a/2)

### Analytic Iwasawa data

Supply native JSON `iwdata` as an object keyed by prime. Ordinary or
multiplicative entries have shape `[lambda, mu]`, and signed entries
have shape `[lambdaPlus, lambdaMinus, commonMu]`. The markers
`"a"`, `"o?"` and `"s?"` preserve additive and unknown statuses.
The equivalent Lean inputs are `iwasawaData` and `iwasawaThreshold`.

The `IntegralCurveProofs.iwasawa` attachment anchors all prime data to
the cusp form's actual arithmetic Fourier coefficients and to rational
modular symbols normalized by the full minimal real period. Integral
finite-level congruences connect these symbols to the proposed power
series for the trivial tame character. The verifier checks the
ordinary and multiplicative normalization at odd primes, and the
trace-zero signed normalization at good primes at least five.
Certified values follow from the least p-adic coefficient valuation
and its first occurrence. The consumer can access the matched prime
evidence through `Name.certificate.iwasawa`. Unknown rows or rows
without evidence remain in the input.

A positive `iwp0` requires evidence covering every good prime at or
above the submitted prime. The local augmentation conditions imply
vanishing for the applicable ordinary or signed series at each such
prime. Above the bound, the evidence supplies existence of the
applicable series and the argument gives vanishing for every
interpolant with that normalization. Zero is the producer's sentinel.
The conditional 11.a2 fixture derives the row at three and the
threshold seven from its independently supplied symbols and
interpolation assumptions.
[ecdata producer](https://github.com/JohnCremona/ecdata/blob/master/scripts/files.py)
· [Pollack's implementation](https://github.com/rpollack9974/Iwasawa-invariants)
· [LMFDB Iwasawa conventions](https://www.lmfdb.org/knowledge/show/ec.iwasawa_invariants)

### Geometric endomorphisms, minimum twists and modified Szpiro ratio

Use `with_proofs` with an `IntegralCurveProofs` attachment. Its
`complexMultiplication` field supplies the ring isomorphism over the separable
closure. The `minimumQuadraticTwist` attachment supplies the fundamental
discriminant, rational change of variables, globally minimal integral candidate
and conductor comparison against every quadratic twist. The two raw twist
claims are compared independently with the fields of that same attachment.
The optional `certificate.minimumQuadraticTwist.uniqueMinimum` evidence
proves the reduced model and discriminant are unique in the ordinary non-CM
case. LMFDB’s ordering for ties, including special j values, requires
separate evidence. [LMFDB producer](https://github.com/JohnCremona/ecdata/blob/master/scripts/min_quad_twist.py)

For `szpiro_ratio`, supply a `modifiedSzpiroRatio` attachment proving global
minimality and identifying the norm of TauCeti’s algorithmic conductor. JSON
accepts an exact decimal center and a `szpiro_ratio_evidence` object whose
`error` is a nonnegative exact rational. Mathlib’s directed dyadic logarithm
checks the claimed error against the two logarithms. Each checked result is
available in the correspondingly named field of `Name.certificate`.


## Remaining cases and proof production

The current checks cover the cases and evidence described above. The
following work would extend that support or construct evidence that the
verifier currently requires from the caller.

| Group / fields | Proof work still needed |
| --- | --- |
| Specific additive `kodaira_symbol`, intrinsic local epsilon factors, other `tamagawa_number` branches | Export the existing transcript checks with the appropriate geometric/local compatibility. Tamagawa-group cardinalities need their own proofs; they are not covered by the current authorized assumption. |
| Tighter torsion bounds and `intrinsic_torsion` | Construct tight bounds for the rational torsion group and evaluate the catalogue pairing when the group is nontrivial. |
| `rank`, `rank_bounds`, `ngens`, `num_int_pts` | Rank intervals can be supplied as Lean proofs and are checked against the actual rational point group; exact rank requires a singleton interval. `ngens` checks only the length of the supplied generator list, not that it is a basis. Integral-point counts can use supplied exhaustive support; deriving it automatically still needs a bound and complete search. |
| CM and minimum twist evidence production | A geometric endomorphism-ring classifier and a general minimum-conductor twist algorithm. Native ordering among equally good twists is a separate open obligation. |
| Heights, periods, regulator, Faltings data, special values | Verified numerical enclosures tied to the actual mathematical definitions. Stored real literals are not exact rational equalities. |
| Algebraic Sha | A separate cohomological/descent proof of finiteness, cardinality, or a primary component. |
| Additional Galois-image cases, Serre data beyond the supported semistable case, and extension torsion proof production | The relevant representations, group images, and constructions of full torsion presentations over the reported extensions. |
| Catalogue labels, orderings and hashes | Produce the complete rosters, compatible curve models and verified coefficient lists required by the corresponding checkers. |

Mazur's classification restricts rational elliptic-curve torsion over `ℚ` to
cyclic groups or groups of the form `ℤ/2ℤ × ℤ/2mℤ`. The checked outputs cover
both shapes when witnesses are supplied; higher invariant-factor
decompositions are not an integration target. Remaining torsion work includes
constructing tight bounds and verifying `intrinsic_torsion`.
