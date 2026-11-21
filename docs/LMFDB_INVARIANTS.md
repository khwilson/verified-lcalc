# LMFDB invariants through `certify_ec`

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
| `jinv` | `jInvariant` | Equality with Mathlib's actual rational-curve `j`. Accepts an exact numerator/positive-denominator pair, fraction string, or integer. |
| `signD` | `discriminantSign` | Equality with the sign of the equation's Δ. |
| `absD` | `minimalDiscriminantAbs` | Actual TauCeti `IsGlobalMinimal` together with the claimed absolute discriminant; requires checked `minimality`. |
| `bad_primes` | `badPrimes` | Complete, duplicate-free prime-divisor list of the minimal discriminant, and equivalence with non-elliptic finite-field reduction; requires `minimality`. |
| `num_bad_primes` | `numBadPrimes` | Cardinality of Mathlib's prime-factor set of the minimal discriminant; requires `minimality`. |
| `ap` / `aplist` | `primeCoefficients` | Actual `LFunction p` coefficients with proved sufficient local minimality checks. |
| `anlist` | `dirichletCoefficients` | Actual consecutive `LFunction n` coefficients; requires `minimality`. Native JSON starts with a₀=0, which is checked and removed; direct Lean lists start at a₁. |
| `conductor` | `conductor` | Identification with the chosen modular realization's level; requires `minimality`, `localData`, and the existing modularity/arithmetic-compatibility axiom. |
| `global_root_number` | `rootNumber` | Identification with that realization's global root/Fricke sign under the same conditions. This is an explicit extension key, not the local-table `root_number`. |
| Integral coordinates / stored x-values | `integralCoordinates` | Point membership; not completeness of the integral-point set. |
| Point-index requests | `infiniteOrderPoints`, `independentPoints` | Infinite order and algebraic-rank lower bounds, with an explicit independence proof for a requested family. |
| Complete numerical payload | `centralResult`, `derivativeResult` | Existing analytic-rank-zero/one certificates under the documented modularity assumption. |

All equation invariants, minimality, bad-prime, and coefficient results have only
standard Lean axiom dependencies. Conductor and global-root identification are
explicitly conditional. Supplying `minimality` also exports `global_minimal`.
None of these checks certifies an external label or database provenance.

`root_number` in an `ec_localdata` row is **local**, at that row's `prime`.
It is deliberately not decoded as a global sign. The local reduction table is
not the same data format as the supplied checked Tate transcripts in `localData`.

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
| `semistable`, `squarefree_disc`, `potential_good_reduction` | Connect finite arithmetic criteria to the canonical reduction predicates; use TauCeti's semistability API rather than introduce another predicate. |
| Local `conductor_valuation`, `discriminant_valuation`, `j_denominator_valuation`, `kodaira_symbol`, `reduction_type`, `root_number`, `tamagawa_number`, and `tamagawa_product` | Export the existing transcript checks with the appropriate geometric/local compatibility. Tamagawa-group cardinalities need their own proofs; they are not covered by the current authorized assumption. |
| `gens`, `torsion_generators`, `torsion`, `torsion_structure`, `torsion_primes`, `intrinsic_torsion` | Normalize rational point coordinates; prove generator orders, independence, and a torsion upper bound. Membership alone does not prove subgroup order or exhaustivity. |
| `rank`, `rank_bounds`, `ngens`, `num_int_pts` | Lower bounds already have the explicit independence route. Exact rank needs an upper-bound/descent certificate; integral-point counts need completeness proofs. |
| `isogeny_degrees`, `isogeny_matrix`, `class_deg`, `class_size` | Certified maps, degrees, and completeness of the represented isogeny class, using TauCeti's isogeny API. |
| `cm`, quadratic-twist fields | Actual endomorphism/twist statements and, for a minimal twist, the required minimality comparison. A j-value lookup alone is not a CM certificate. |
| Modular `degree`, `manin_constant`, `optimality` | Statements about the modular parametrization, not the degree of an arbitrary isogeny. |
| Heights, periods, regulator, Faltings data, special values, `abc_quality`, `szpiro_ratio` | Verified numerical enclosures tied to the actual mathematical definitions. Stored real literals are not exact rational equalities. |
| `sha`, `sha_an`, `sha_primes` | Cohomological/descent proofs and a precise analytic-vs-algebraic interpretation; no BSD axiom is authorized. |
| Galois-image, adelic, nonmaximal-prime, Serre, Iwasawa, and torsion-growth data | The relevant representations, fields, group images, and completeness proofs. |
| Labels, ordering/index fields, hashes | Catalogue/provenance metadata; not mathematical identity certificates. |

The next arithmetic integration targets are canonical semistability and local
reduction fields, followed by rational torsion-point certificates and upper bounds.
