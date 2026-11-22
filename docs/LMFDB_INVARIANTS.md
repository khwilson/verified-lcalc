# LMFDB invariants through `certify_ec`

The [EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md) inventories the related LMFDB tables and specifies the reusable theorem and checker work for each remaining field.

`certify_ec` remains the sole public interface. Each optional witness field
requests a check against the represented curve. Missing fields make no claim.
For a recognized field whose required arithmetic evidence is absent, the command
reports it as unverified and emits no mathematical correctness theorem for it.
Incorrect supplied evidence or a failed supported check rejects the entire
certificate. `claimed_*` definitions and `*_input_eq` bindings record input;
they do not themselves assert that its value is correct.

The field inventory was checked against the live
[curve schema](https://www.lmfdb.org/api/ec_curvedata/),
[37.a1 data and related tables](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1),
and [local-data schema](https://www.lmfdb.org/api/ec_localdata/).

## Checks implemented

| JSON data | Lean witness field | Mathematical output / required evidence |
| --- | --- | --- |
| `ainvs` | `equation` | Actual Mathlib `WeierstrassCurve ℤ`; nonsingularity is checked. |
| `binvs`, `cinvs` | `bInvariants`, `cInvariants` | Equalities with Mathlib's b₂,b₄,b₆,b₈ and c₄,c₆. These are optional equation-data extensions. |
| `discriminant` | `discriminant` | Equality with this supplied equation's Mathlib Δ; does not assert minimality. |
| `abc_quality` with `abc_quality_evidence` | `abcQuality` | Proved absolute error bound between the reported decimal and TauCeti’s real abc quality, using the factorization in the evidence. |
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
| `ap` / `aplist` | `primeCoefficients` | Actual `LFunction p` coefficients with proved sufficient local minimality checks. |
| `anlist` | `dirichletCoefficients` | Actual consecutive `LFunction n` coefficients; requires `minimality`. Native JSON starts with a₀=0, which is checked and removed; direct Lean lists start at a₁. |
| `conductor` | `conductor` | Identification with the chosen modular realization's level; requires `minimality`, `localData`, and the existing modularity/arithmetic-compatibility axiom. |
| Local `conductor_valuation` | `localInvariants[].conductorValuation` | Proves primality and the claimed exponent in the Mathlib factorization of the curve's checked modular level. Requires a checked `conductor` with `minimality` and `localData`. |
| `global_root_number` | `rootNumber` | Identification with that realization's global root/Fricke sign under the same conditions. This is an explicit extension key, not the local-table `root_number`. |
| `integral_points` | `integralCoordinates` | Point membership on the supplied equation. |
| `xcoord_integral_points` | `integralFiberRoots` | Complete finite y-fibers at the listed x-values, with a double root represented once. The theorem makes no claim over other x-values. |
| `gens`, `torsion_generators` | `generatorCoordinates`, `torsionGeneratorCoordinates` | Exact weighted triples decode to rational points with checked membership. |
| `torsion_generator_orders` | `torsionGeneratorOrders` | Project-specific list giving an exact additive order for each supplied torsion generator point. |
| Point-index requests | `infiniteOrderPoints`, `independentPoints` | Infinite order and algebraic-rank lower bounds, with an explicit independence proof for a requested family. |
| `torsion_bound` | `torsionBound` | Two odd good-reduction primes and the claimed positive gcd of their finite point counts. The full rational torsion order divides that gcd. |
| `torsion` | `torsion` | Claimed exact order. A gcd of one proves the exact cardinality. For a larger checked bound the claimed order must be positive and divide the bound. |
| Complete numerical payload | `centralResult`, `derivativeResult` | Existing analytic-rank-zero/one certificates under the documented modularity assumption. |

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

A local row requires `prime`. An optional valuation gives its exponent in the absolute minimal
discriminant, the reduced rational denominator of `j`, or the checked modular level. Conductor
exponents may be supplied for any rational prime and are zero when that prime does not divide the
level. The reduction codes are 0 for additive, 1 for split multiplicative, and −1 for nonsplit
multiplicative reduction. Certificates cover each supplied row individually.

`root_number` in an `ec_localdata` row is **local**, at that row's `prime`.
It is deliberately not decoded as a global sign. The local reduction table is
not the same data format as the supplied checked Tate transcripts in `localData`.

`torsion_bound` takes an object with exact integer fields `first_prime`,
`second_prime`, and `bound`. JSON primes are capped at 10000. The checker
verifies odd primality and good reduction of the supplied equation at both
primes, then recomputes the gcd. The resulting `torsion_bound` theorem proves
divisibility and positivity for the bound. A bound of one also exports
`torsion`, the exact cardinality theorem for the group's trivial case.
Larger bounds leave a consistent exact-order claim unverified. A raw
`torsion` value without bound evidence is also unverified.

Import `CertifiedCurves.Invariants` for the small reusable 37.a1 example.
`tests/consumers/CertifiedECInvariantsConsumer.lean` imports its `.olean` theorems
without rerunning the certification command.

## Remaining invariant groups

These fields remain unverified metadata unless a check above independently
covers their mathematical content. A matching list length, product, numerical
approximation, or classification-table entry is not a substitute for the
missing theorem.

| Group / fields | Proof work still needed |
| --- | --- |
| Local `kodaira_symbol`, `root_number`, `tamagawa_number`, and `tamagawa_product` | Export the existing transcript checks with the appropriate geometric/local compatibility. Tamagawa-group cardinalities need their own proofs; they are not covered by the current authorized assumption. |
| `gens`, `torsion_generators`, nontrivial `torsion`, `torsion_structure`, `torsion_primes`, `intrinsic_torsion` | Match verified point orders and independence with a tight divisor to prove generation. |
| `rank`, `rank_bounds`, `ngens`, `num_int_pts` | Lower bounds already have the explicit independence route. Exact rank needs an upper-bound/descent certificate; integral-point counts need completeness proofs. |
| `isogeny_degrees`, `isogeny_matrix`, `class_deg`, `class_size` | Certified maps, degrees, and completeness of the represented isogeny class, using TauCeti's isogeny API. |
| `cm`, quadratic-twist fields | Actual endomorphism/twist statements and, for a minimal twist, the required minimality comparison. A j-value lookup alone is not a CM certificate. |
| Modular `degree`, `manin_constant`, `optimality` | Statements about the modular parametrization, not the degree of an arbitrary isogeny. |
| Heights, periods, regulator, Faltings data, special values, `szpiro_ratio` | Verified numerical enclosures tied to the actual mathematical definitions. Stored real literals are not exact rational equalities. |
| `sha`, `sha_an`, `sha_primes` | Cohomological/descent proofs and a precise analytic-vs-algebraic interpretation; no BSD axiom is authorized. |
| Galois-image, adelic, nonmaximal-prime, Serre, Iwasawa, and torsion-growth data | The relevant representations, fields, group images, and completeness proofs. |
| Labels, ordering/index fields, hashes | Catalogue/provenance metadata; not mathematical identity certificates. |

The next arithmetic integration targets include rational torsion-point certificates
and torsion upper bounds.
