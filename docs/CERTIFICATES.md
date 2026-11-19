# Certificate interface, version 1

The certificate interface is implemented in `VerifiedLcalc/Certificate.lean` and
its analytic soundness theorem in `CertificateSoundness.lean`. It separates an
expensive producer, a finite data checker, and proved mathematical evidence.
This format is provisional until a real elliptic-curve evaluation is available.

## Identity

`Artifacts.Request` is the structural identity for a future cache entry:

- Subject: an exact five-integer Weierstrass equation plus arithmetic/unitary
  normalization, or an explicitly separate monomial demo subject.
- Evaluation center: derived from the subject (1, 1/2, or 0 respectively).
- Computation settings: precision bits, term limit, and maximum derivative order.
- Format version, Lean toolchain, mathlib revision, producer revision, and checker
  revision.

Labels, expected database ranks, and externally supplied conductors are not
mathematical identities. In particular, a database match cannot certify a curve.
The eventual elliptic backend must calculate its arithmetic data and prove the
connection to the input equation.

The checker requires exact request equality. `check_request_eq` proves that an
accepted artifact belongs to the requested input and build identity. Negative
examples cover changed subjects, equations, normalization, settings, versions,
wrong ranks, missing evidence, and uncertain vanishing.

Build-identifier strings are bookkeeping, not attestations. The demo uses named
version markers; it does not yet calculate source-content digests. The actual
imported sources and dependencies are tracked by Lake. Before implementing a
persistent content-addressed cache, populate the producer/checker identities from
immutable source revisions or content digests, canonically serialize the full
request, and hash it. Do not use a process-dependent `Hashable` value as a stable
or cryptographic cache identifier.

## Data and mathematical evidence

`Artifact` contains its request, claimed rank r, and r+1 rational derivative
rectangles. The finite `check` checks request equality, format support, the
maximum derivative, exact evidence length, and the first-nonzero-derivative
witness. It does not execute an L-function evaluator.

`validate` constructs a proof-carrying `Checked` payload when this finite check
succeeds. This establishes the payload contract, **not an analytic rank by
itself**: a malicious producer can supply boxes unrelated to its input.

`AnalyticEvidence` supplies the remaining checked Lean proof obligations:

1. The function denotes the requested mathematical subject.
2. It is analytic at the subject's evaluation center.
3. Every rectangle encloses the corresponding true derivative.

`check_sound` proves that accepted data plus these obligations give the exact
analytic order. `check_monomial_sound` specializes this to the named monomial,
using its interpretation proof. There is no function supplied at runtime whose
relationship to the input is silently assumed.

The interpretation currently supports monomials only. Its elliptic-curve branch
is `False`, and `ellipticCurve_not_denotes` proves it is unavailable. This is an
explicit unsupported case, not an axiom or a stand-in analytic function. To add
elliptic curves, first implement the actual L-function definition and its
normalization, extend the interpretation to that definition, then prove the
analytic and enclosure obligations. The first exact curve request is 11.a2,
with coefficients `[0,-1,1,-10,-20]`, at the arithmetic center 1. No artifact
claims its rank yet.

For the real backend, retain intermediate finite sums and certified error bounds
when they make checking cheaper than generation. Derive enclosure proofs from
proved evaluation formulas and explicit tails. Do not prove the final numerical
answer by rerunning the full producer with `decide`. Small exact checks of the
supplied evidence may still use `decide`; an efficient evidence representation
and measured generation/checking costs remain part of the first real case.

## Working demonstration and compiled reuse

Generate the demo as a proper importable Lean module:

```sh
lake exe verified-lcalc tests/VerifiedLcalcTests/Fixtures/Cubic.lean
lake build VerifiedLcalcTests.Fixtures.Cubic
lake env lean tests/consumers/Cubic.lean
```

The generated source contains the finite payload, a theorem that its small check
accepts, its analytic evidence, and the final analytic-order theorem. It imports
existing analytic proofs rather than invoking the producer. The current exact
demo payload is declared in `CertificateDemo.lean`; later producers will emit
computed witnesses instead. The emitted payload is a complete literal, including
all request fields and derivative rectangles, rather than a call back to the
producer. The demo uses Lean's `Repr` for source emission and then checks that
source; this is not a stable canonical interchange encoding or cache hash.

The compiled theorem is available as:

```lean
import VerifiedLcalcTests.Fixtures.Cubic
#check VerifiedLcalcTests.Fixtures.Cubic.certified_analytic_order
```

Lake caches the generated module's `.olean` artifacts in `.lake/build/lib/lean`.
On an unchanged build, importing the theorem reuses them without checking its
source again. Regenerating identical text does not rewrite the file. Changes to
its imported definitions, evidence proofs, or mathematical dependencies cause
Lake to invalidate dependent builds. `tests/consumers/Cubic.lean` is an import-only
consumer, demonstrating this reuse rather than repeating the numerical check.

For a fresh source verification, run:

```sh
lake env lean tests/VerifiedLcalcTests/Fixtures/Cubic.lean
```

This checks the saved witness and analytic evidence again, not the expensive
producer. Importing an `.olean` trusts that compiled artifact's provenance; it is
not a fresh kernel replay. Keep the Lean source and exact dependencies alongside
cached artifacts so replay remains possible.

## Deferred cache infrastructure

No remote cache, digest-to-path store, serializer, or external artifact loader has
been added. The current reuse mechanism is saved Lean modules plus Lake's normal
local artifact cache. When measured real-case costs justify more infrastructure:

1. Derive a canonical request digest from the complete identity above.
2. Store the witness module, metadata, dependencies, and compiled artifacts.
3. Check request equality on retrieval, then either load a trusted compiled
   artifact or rebuild/replay its source.
4. Validate every actual elliptic certificate independently of LMFDB comparison.

Never turn a cache miss, unsupported interpretation, or failed certificate into
an expected rank copied from the regression dataset.

## Numerical rank observations

A separate `NumericalRanks.Artifact` now records a precision policy and a
`numericalLowerBound`, with immutable policy snapshots and exact rational
derivative rectangles. Its checker certifies cutoff containment, and its
semantic theorem proves actual derivative smallness. An additional, explicitly
named vanishing hypothesis is required for an analytic-rank lower bound. This
does not relax the exact certificate format or its singleton-zero requirements.
See [precision policy and replay instructions](NUMERICAL_RANK.md).

## First conditional elliptic rank certificate

`tests/VerifiedLcalcTests/Fixtures/AssumedCurve11Central.lean` pairs the saved
53-bit/eight-term payload with a proved actual coefficient prefix, the actual
L-function's global tail bound, and the modularity-dependent continuation.
`analytic_rank_zero` has no remaining proof parameters. Its executable
`certifiedRank` carries the exact analytic-order theorem in its type; evaluating
`certifiedRank.val` returns 0 after proof erasure. The import-only consumer is
`tests/consumers/AssumedCurve11Central.lean`; it prints both the axiom dependencies
and the rank. Replaying the source checks the full proof instead of importing
its previously compiled theorem.

The optional regression cache keys this certificate by exact curve equation
and conductor. Its returned number is proved sound separately in
`Assumptions/Regression.lean`. This is a local compiled-certificate cache, not
an LMFDB expected-rank lookup. Shared storage and authenticated request digests
remain future work.

## First derivatives and exact rank one

The derivative certificates use the same saved-theorem model. Each `certifiedRank`
contains the proved equality of analytic order with one. The central zero is
exact, from the negative functional-equation sign; a rigorous first-derivative
enclosure proves nonvanishing. No small-value threshold is used as exact
vanishing evidence. The mathematical derivation, interval algorithm and replay
commands are documented in [FIRST_DERIVATIVE.md](FIRST_DERIVATIVE.md).

The optional rank-one registry is separate from the rank-zero registry. Both are
bound to the exact input equation and conductor by a kernel-checked soundness
theorem for the combined backend. Registry installation is transactional across
both source files and compiled dependencies. The derivative report and proof
bundle hashes live under `output/derivative/`.
