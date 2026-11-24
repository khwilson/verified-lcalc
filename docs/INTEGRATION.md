# TauCeti and mathlib integration

Workflow status (2026-11-19): legacy batch/derivative/conductor generators,
`lmfdb-check`, generated registries and bulk certificate directories described
below have been retired. Their command examples and cache counts are historical,
with implementation preserved in baseline commit `fcdc4f2`. The mathematical
proof engine remains; use [`certify_ec`](CERTIFY_EC.md) for current witness
verification and importable theorem generation.

The modularity axiom is unchanged. No numerical bound, evaluation formula,
vanishing principle or extra arithmetic axiom was added.

## Completed connections

The project imports TauCeti through the package pinned in the [build guide](BUILD.md).
The original integration used selected source excerpts. Their [historical
provenance](../VerifiedLcalc/Upstream/TauCeti/README.md) records those revisions and adaptations.

- `EllipticCurve/TauCeti.lean` connects the executable point counts and traces
  with TauCeti's projective-model definitions, including singular reductions.
  It identifies local polynomials, inverse power series and formal Dirichlet
  coefficients when the required minimal-reduction equivalence is supplied.
- `EulerProduct.lean` proves that at a prime power, factors with coprime bases
  contribute only their constant coefficient. Mathlib's coefficientwise
  stabilization theorem then extracts that coefficient from the infinite
  formal Euler product.
- `RationalPrimes.lean` transports prime ideals of O_Q to Z, proves their norms
  are prime and proves the norm distinguishes the prime ideals.
- TauCeti's completion theorem identifies the completed valuation-ring
  residue field with the original ideal quotient. `GlobalCoefficients.lean`
  consequently identifies each actual global LFunction coefficient at p^k
  with the corresponding local power-series coefficient.
- `GlobalBounds.lean` proves the prime-power recurrence and the global bound
  `|LFunction n| <= n^3` for actual rational-curve coefficients. This uses the
  actual chosen minimal reductions and elementary point counting, without an
  input-equation compatibility assumption or modularity axiom. At bad
  reduction it also proves the first coefficient has absolute value at most 1.
- `Assumptions/Fourier.lean`, `CentralSeries.lean` and
  `Numerics/ExponentialIntegral.lean` derive the central exponential HasSum
  formula, including justified termwise integration. The curve-specific
  formula now needs only a supplied modular realization; the global bound is
  proved. `CentralEvaluator.lean` constructs CentralSeriesEvidence from the
  finite actual coefficient prefix and identifies a separated interval with
  analytic order zero.

## First complete conditional numerical certificate

`tests/VerifiedLcalcTests/Fixtures/AssumedCurve11Central.lean` proves

    analyticOrderAt AssumedCurve11.continuedL 1 = 0.

It has no remaining arithmetic or numerical proof arguments. Its only custom
axiom is the existing `ellipticModularity` assumption. It uses the saved
53-bit, eight-term payload from `tests/VerifiedLcalcTests/Fixtures/Curve11Central.lean`.

The good-prime fields of the modular realization identify the coefficients at
2, 3, 5 and 7 with our checked point counts. The actual coefficient at 2 is -2,
so the proved bad-reduction bound rules out a bad local factor there. The
proved recurrence gives coefficients at 4 and 8, and multiplicativity gives 6.
This establishes the entire finite prefix. The actual global n^3 bound controls
all remaining coefficients, including those at bad primes. No database rank
or numerical-zero cutoff participates in the proof.

The theorem is paired with executable data in `certifiedRank`. Run:

    lake build VerifiedLcalcTests.Fixtures.AssumedCurve11Central
    lake env lean tests/VerifiedLcalcTests/Fixtures/AssumedCurve11Central.lean
    lake env lean tests/consumers/AssumedCurve11Central.lean

The final consumer imports the cached checked theorem, prints its axiom
list, and evaluates the certified rank value to 0.

## Conditional regression cache

`Regression/ConditionalCore.lean` provides a small runtime cache keyed by the
exact equation and conductor, independent of labels and expected ranks.
`Assumptions/Regression.lean` proves every returned rank equals the analytic
order of that input's modularity-dependent continuation.

    lake exe lmfdb-check --conditional

This opt-in mode labels the dependency on ellipticModularity. It currently
reports 70 matches, 0 mismatches and 30 inconclusive cases, and exits 1 because
coverage is incomplete. The default regression remains separate and does
not advertise assumption-dependent results as unconditional.

## Remaining work

The local minimal-model/residue-field compatibility is now proved uniformly
for semistable integral equations. For a general evaluator, extend this to
arbitrary input equations and additive reduction, including conductor/sign
compatibility. The global Euler-product extraction and global coefficient
bound are proved. The first example succeeds without requiring a general
minimal-model identification because its short prefix can be determined by
the argument above.

Then derive derivative kernels, certified evaluations and tails through order
four. The existing conditional central vanishing for 37.a1 proves only a rank
lower bound; proving its first derivative nonzero remains the next rank-one
example. Broader reduction handling, full regression coverage and shared
certificate caching follow. Exact vanishing remains separate from the global
precision policy.

## Verification

    lake build
    lake build VerifiedLcalc.Assumptions.Regression
    lake env lean tests/audits/AuditArithmetic.lean
    lake env lean tests/audits/AuditIntegration.lean
    lake env lean tests/audits/Audit.lean
    lake env lean tests/audits/AuditAssumptions.lean

The integration audit checks the general arithmetic/analytic implications for
standard foundational axioms only. The separate assumption audit guards the
concrete rank-zero certificate and the conditional cache soundness theorem for
exactly those foundations plus ellipticModularity. Fresh and compiled
certificate replays and both regression modes are checked separately.

Validation for the rank-zero milestone: full default and conditional-module
builds passed; all three audits passed; fresh and cached cubic and 11.a2
rank-zero certificate replays passed. The cached rank-zero consumer evaluated
the certified value to 0. The conditional regression returned 1 match,
0 mismatches and 99 inconclusive cases (exit 1); the default mode returned
100 inconclusive cases (exit 1). The mathlib pin remains unchanged and its
checkout has no source modifications. All ten ported-source hashes were checked.

## Automated batch milestone

The per-curve coefficient argument is now replaced by the proved
`prefixSupported` criterion and the uniform `certifySemistableCentral` theorem.
`lake exe certify-batch` automates candidate search, arithmetic and
interval proof generation, kernel replay, axiom guards, registry proof and
strict regression. Its first completed run produced 18 checked conditional
rank-zero certificates and 18 reference matches, with 82 cases explicitly
inconclusive. See [BATCH.md](BATCH.md) and `output/batch/report.json` for statuses.

## Uniform semistable arithmetic

The broader arithmetic engine now proves input-model minimality, residue-field
identification, invariance of reduction counts, all local Euler factors and
all coefficient prefixes for semistable integral models. It has no modularity
or other custom axiom. The batch route no longer needs a trace-size prefix
criterion and now yields 70 checked conditional rank-zero results, with the
remaining 30 explicitly unresolved. See
[ARITHMETIC_ENGINE.md](ARITHMETIC_ENGINE.md).

The additive arithmetic extension covers all 26 fixture models outside the
semistable criterion, including the borderline 2-adic model 32.a4. Their complete
coefficient-prefix proofs and local additive factors are independent of modularity.
The rank registry remains at 70; additive conductor and root-number compatibility
remain explicit obligations in `certifyMinimalCentralModel`. See
[ADDITIVE_REDUCTION.md](ADDITIVE_REDUCTION.md).
