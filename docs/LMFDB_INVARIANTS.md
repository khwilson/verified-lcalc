# LMFDB invariants through `certify_ec`

The [EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md) inventories the related LMFDB tables and specifies the reusable theorem and checker work for each remaining field.

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
| `ec_galrep` | 7 | The generator field is checked at the reported finite modulus in a proved torsion basis. G1 covers the remaining image data. |
| `ec_padic` | 5 | Stored class rows remain report-only. A curve-level encoding of the rank-zero display is checked as a p-adic ball at a good ordinary prime. |
| `ec_torsion_growth` | 4 | The checked field and degree include evidence of strict torsion growth. G2 specifies the full group and primitive growth. |
| `ec_iwasawa` | 3 | G3 specifies prime-indexed invariants and the uniform assertion made by a positive threshold. |

The command covers **57 of 85 distinct LMFDB column names** with the evidence
specified below. Assigning each name to one table where its interpretation
has a checker gives 33 in `ec_curvedata`, 3 in `ec_classdata`, 10 in
`ec_mwbsd`, 8 in `ec_localdata`, 1 in `ec_galrep`, and 2 in
`ec_torsion_growth`. Shared names such as `class_size` count once.
Project-specific keys are excluded. The four ball coordinates shared with
`ec_padic` can be checked for the curve-level rank-zero display, which
LMFDB computes directly. They add zero stored-column claims to this count.

Count coverage by the mathematical assertion and the evidence a consumer can
project. For example, `ec_curvedata.torsion` is a cardinality over ℚ, while
`ec_torsion_growth.torsion` gives invariant factors over a specified extension.
The former can be proved through `certificate.torsion.cardinality`. The latter
has its own roadmap target. The public contract index lists the canonical Lean
modules as the migration proceeds. [Contract index](CERTIFICATE_CONTRACT_LAYOUT.md)
· [Roadmap targets](roadmaps/LMFDB_Q_CERTIFICATION.md)

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
| `tamagawa_number` | `localInvariants` row field `tamagawaNumber` | Exact intrinsic Tamagawa number at a prime of good or `I₁` reduction. A local test proves minimality at that prime. |
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
| `adelic_gens` | `adelicGenerators` | Complete image on the full geometric torsion of the reported modulus in a supplied basis. Requires an `FiniteGaloisImageFact` through `with_proofs`. |
| `num_int_pts` | `numIntegralPoints` | Exact cardinality theorem from supplied exhaustive `IntegralXSupport`; available at `certificate.algebraic.completeIntegralPoints` with finite-set completeness and `Finite` evidence. Without support it is unverified, but a count below the number of distinct checked points or seed-fiber solutions is rejected. |
| `gens`, `torsion_generators` | `generatorCoordinates`, `torsionGeneratorCoordinates` | Exact weighted triples decode to rational points with checked membership. |
| `rank`, `rank_bounds` | `algebraicRank`, `algebraicRankBounds` | Verify supplied endpoints against a typed proof of bounds on the actual Mordell–Weil rank. A singleton proof gives exact rank. |
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

`tamagawa_number` currently verifies the value one for good reduction and
multiplicative reduction of index one. The equality concerns TauCeti's
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


## Remaining invariant groups

These fields remain unverified metadata unless a check above independently
covers their mathematical content. A matching list length, product, numerical
approximation, or classification-table entry is not a substitute for the
missing theorem.

| Group / fields | Proof work still needed |
| --- | --- |
| Specific additive `kodaira_symbol`, intrinsic local epsilon factors, other `tamagawa_number` branches | Export the existing transcript checks with the appropriate geometric/local compatibility. Tamagawa-group cardinalities need their own proofs; they are not covered by the current authorized assumption. |
| Tighter torsion bounds and `intrinsic_torsion` | Construct tight bounds for the rational torsion group or prove the required torsion pairing statement. |
| `rank`, `rank_bounds`, `ngens`, `num_int_pts` | Rank intervals can be supplied as Lean proofs and are checked against the actual rational point group; exact rank requires a singleton interval. `ngens` checks only the length of the supplied generator list, not that it is a basis. Integral-point counts can use supplied exhaustive support; deriving it automatically still needs a bound and complete search. |
| CM and minimum twist evidence production | A geometric endomorphism-ring classifier and a general minimum-conductor twist algorithm. Native ordering among equally good twists is a separate open obligation. |
| Modular `degree`, `manin_constant`, `optimality` | Statements about the modular parametrization, not the degree of an arbitrary isogeny. |
| Heights, periods, regulator, Faltings data, special values | Verified numerical enclosures tied to the actual mathematical definitions. Stored real literals are not exact rational equalities. |
| Algebraic Sha | A separate cohomological/descent proof of finiteness, cardinality, or a primary component. |
| Remaining Galois-image levels, Serre and Iwasawa data, and full extension torsion | The relevant representations, fields, group images, and completeness proofs. |
| Labels, ordering/index fields, hashes | Catalogue/provenance metadata; not mathematical identity certificates. |

Mazur's classification restricts rational elliptic-curve torsion over `ℚ` to
cyclic groups or groups of the form `ℤ/2ℤ × ℤ/2mℤ`. The checked outputs cover
both shapes when witnesses are supplied; higher invariant-factor
decompositions are not an integration target. Remaining torsion work includes
constructing tight bounds and verifying `intrinsic_torsion`.
