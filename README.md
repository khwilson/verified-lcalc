# verified-lcalc

Lean 4 arithmetic and interval evaluation for certified elliptic-curve
analytic-rank computations. The current 1,100-curve regression has **822 checked
conditional exact rank-zero certificates**, **228 checked conditional exact
rank-one certificates**, **zero reference mismatches**, and **50 inconclusive
exact ranks**. The remaining gaps are 48 unresolved minimality criteria, an
unseparated central value for 389.a1, and an unseparated first derivative for
5077.a1. See the [first-derivative backend](docs/FIRST_DERIVATIVE.md) and
[the wild additive backend](docs/WILD_ARITHMETIC.md).

The finite algorithms and their agreement with mathematical formulas are
kernel-checked. Analytic elliptic-curve certificates depend on the explicitly
authorized temporary general-modularity axiom, including standard arithmetic
conductor/root-number compatibility. Geometric Tate/Ogg/Halberstadt
compatibility remains assumed in that package; numerical enclosures and
nonvanishing are proved. Derivatives of order two and higher and a complete lcalc translation remain
unfinished.

The main demo executable also emits a fully checked cubic certificate for
`f(z)=z^3` at zero. Elliptic rank certificates are produced by `ec-batch` and
checked/installed by `certify-batch`; `negative-certificates --check` separately
checks lower bounds. `derivative-batch` and `certify-derivatives` produce and
check exact rank-one certificates. Compiled proofs can be reused with
`certify-batch --seal-cache` and `certify-derivatives --seal-cache`. Every individual curve keeps a public module, backed by shared
checked proof bundles.

The [certificate interface](docs/CERTIFICATES.md) now separates producer output,
finite checking, and analytic evidence. Requests identify the exact equation,
normalization, settings, format, and build versions. The saved demo is an
importable Lean module whose compiled theorem Lake can reuse.

The [elliptic arithmetic backend](docs/ELLIPTIC_BACKEND.md) now computes exact
good-prime point counts, Frobenius traces, and local prime-power coefficients,
with proofs against mathlib's actual curve-point type and formal Euler factors.
It includes a real-curve arithmetic certificate for 11.a2. This arithmetic
layer supplies the coefficients used by the subsequent analytic evaluator. [The infrastructure audit](docs/INFRASTRUCTURE.md)
records TauCeti prerequisites and the integrated adapter to David Ledvinka's
mathlib dyadic interval machinery and a pinned exponential extension. Signed
finite exponential sums, elliptic evaluation formulas and tail bounds have
enclosure proofs.

The [numerical precision policy](docs/NUMERICAL_RANK.md) defaults to 53 bits
and an exact cutoff of 1/33554432. Separate certificates record numerical
lower bounds, with proofs of derivative smallness and explicitly conditional
analytic lower bounds. These observations do not replace exact vanishing proofs.

The [central-expression evaluator](docs/CENTRAL_EVALUATOR.md) now combines
model Euler coefficients, proved exponential bounds, an enclosure of
`2*pi/sqrt(N)`, and a rigorous geometric tail theorem. It can save replayable
Lean payloads. Its actual elliptic L-value interpretation remains conditional
on explicit series and arithmetic evidence. The [first-derivative backend](docs/FIRST_DERIVATIVE.md)
proves the Mellin differentiation formula, logarithmic interval quadrature and
infinite-tail bounds needed for exact rank-one certification.

## Run

This workspace uses the adjacent `../mathlib4` checkout, at revision
`3440367ed1804626334f13a3a534a9cbb3385a59`, and Lean `v4.36.0-rc2`.
See [build instructions](docs/BUILD.md) for a standalone checkout and cache use.

```sh
lake build
lake exe precision-policy
lake env lean certificates/NumericalQuartic.lean
lake exe verified-lcalc VerifiedLcalc/Certificates/Cubic.lean
lake build VerifiedLcalc.Certificates.Cubic
lake env lean certificates/Cubic.lean
lake env lean Audit.lean
lake exe exp-enclosure -1 0 24
lake exe ec-coefficients --curve 11.a2
lake exe ec-coefficients --summary
lake exe ec-central 11.a2 1 32
lake env lean certificates/Curve11Central.lean
lake env lean VerifiedLcalc/Certificates/Curve11Arithmetic.lean
lake exe lmfdb-check --inventory
lake exe lmfdb-check
```

The last command intentionally exits **1**: the default axiom-free rank
backend leaves all 1,100 curves inconclusive. The opt-in `--conditional` mode
uses the checked modularity-dependent cache and currently reports 1,050 matches,
zero mismatches and 50 inconclusive inputs, so it also exits 1. `--inventory`
exits 0 after fixture validation and reporting; it does not assert complete
analytic-rank coverage.

## Guarantees

- `Scan.lean` uses exact rational rectangles. `scan_correct` proves that a
  successful search has singleton-zero rectangles at every earlier index and
  a rectangle excluding zero at the returned index. Exhaustion, uncertainty,
  and malformed bounds encountered during the search return `none`.
- `Analytic.lean` proves `scan_analyticOrderAt`: for an analytic complex function,
  **proved enclosures of its actual iterated derivatives** turn a successful
  search into its exact order of vanishing. The result remains in ℕ∞ until a
  finite order is established; no infinity-to-zero conversion is used.
  Rectangle containment uses mathlib's `Set.Icc` for each real coordinate;
  the runtime `Box` stores only the exact rational endpoints.
- `computeRank` returns a natural number with a proof of that equality. Analyticity
  and enclosure proofs are required arguments, not runtime assertions or axioms.
- `Demo.lean` checks empty input, uncertain boxes, invalid bounds, imaginary
  nonvanishing, and an uncertain earlier derivative followed by a nonzero one.
  `Examples.lean` proves the polynomial's derivative enclosures and analytic rank.
- The executable imports only the small core. The emitted certificate imports
  the analytic proof library and checks its finite payload with `decide`.
  Proof checking does not rely on trusting executable output or `native_decide`.
- `Certificate.lean` checks request identity and finite derivative evidence.
  `CertificateSoundness.lean` proves that accepted evidence, with its semantic
  interpretation and derivative-enclosure proofs, establishes the exact analytic
  order. Unsupported elliptic-curve interpretations cannot supply those proofs.
- `VerifiedLcalc/Certificates/Cubic.lean` is the saved certificate source;
  `certificates/Cubic.lean` demonstrates importing its compiled theorem. To
  replay the source afresh, run `lake env lean VerifiedLcalc/Certificates/Cubic.lean`.
  No persistent content-addressed or remote cache is implemented yet.

Each implemented computation routine has a corresponding correctness theorem.
Definitions such as `Box.Contains` and `Encloses` are specifications. Command-line
I/O is outside the proved mathematical core; the emitted Lean theorem checks its
output independently. Standard Lean/mathlib foundations are audited in
[Audit.lean](Audit.lean). The default modules have no project axioms or `sorry`.
An opt-in [modularity assumption](docs/ASSUMPTIONS.md), explicitly authorized by
the user, supports separately labelled conditional elliptic theorems and has its
own `AuditAssumptions.lean`. The conditional
[37.a1 certificate](VerifiedLcalc/Certificates/AssumedCurve37.lean) proves exact
central vanishing and analytic rank at least one from its computed negative
sign. It does not yet prove exact rank one. See
[the proof boundary](docs/VERIFICATION.md). The
[TauCeti/mathlib integration](docs/INTEGRATION.md) now derives the central
exponential formula and interval connection. The actual global coefficient
bound is proved, and the
[11.a2 certificate](VerifiedLcalc/Certificates/AssumedCurve11Central.lean)
proves exact rank zero conditional only on the named modularity axiom.
`lake env lean certificates/AssumedCurve11Central.lean` prints the certified
value 0 and its axiom dependencies. `lake exe lmfdb-check --conditional` uses
the separately proved conditional certificate cache; incomplete coverage
still fails.

## LMFDB regression data

[data/lmfdb-100.json](data/lmfdb-100.json) and
[VerifiedLcalc/Lmfdb.lean](VerifiedLcalc/Lmfdb.lean) contain the same 100 cases,
recorded from LMFDB on 2026-11-17. Each case includes the LMFDB label, conductor,
five exact Weierstrass coefficients, and the **analytic_rank** field. The JSON
also records source URLs. The sample uses the first API page, replaces `42.a5`
and `42.a6` with `389.a1` and `5077.a1`, and covers ranks 0, 1, 2, and 3.
Distribution: 96 rank 0, 2 rank 1, 1 rank 2, 1 rank 3. It is a small-conductor
smoke sample with repeated isogeny classes, not a balanced or representative
benchmark.

Lean checks the count, distinct labels, and rank coverage. `Regression.lean`
passes only curve inputs to a backend, keeps expected ranks separate, and proves
that an `agree` outcome is equivalent to a returned value matching the reference.
It does not infer analytic correctness from database agreement. Replace
`pendingBackend` with the proved backend when available; default strict mode
requires all 1,100 current inputs to resolve and match. Analytic certificates
are replayed separately; inconclusive inputs fail the coverage gate.

Sources: [LMFDB API](https://www.lmfdb.org/api/ec_curvedata/),
[389.a1](https://www.lmfdb.org/EllipticCurve/Q/data/389.a1),
[5077.a1](https://www.lmfdb.org/EllipticCurve/Q/5077/a/1).

## Automated conditional batch

Run `lake exe certify-batch` to search all 1,100 inputs, generate
conditional central-value certificates, kernel-check them, install the proved
cache and run the strict regression. This automates the supported arithmetic
and central-evaluation route; unsupported cases retain explicit reasons.
See [BATCH.md](docs/BATCH.md) for the proof boundary, adaptation and outputs.

The [broader arithmetic engine](docs/ARITHMETIC_ENGINE.md) now proves all
local factors and coefficient prefixes for semistable integral models,
including bad primes. The batch checker uses this proof directly; its former
trace-size prefix restriction is removed. The arithmetic itself adds no axiom.

With the expanded fixture, the combined conditional regression reports **1,050
matches, 0 mismatches and 50 inconclusive cases**. The strict coverage gate fails until
every case resolves. Finite arithmetic-to-formula proofs add no custom axiom;
analytic certificates depend on the authorized general-modularity package,
including its explicit standard conductor/root-number compatibility fields.

Additive reduction arithmetic covers the original 26 equations excluded by
the semistable criterion, including 32.a4. Run `lake exe additive-witnesses --check`
for kernel replay and `lake env lean AuditAdditive.lean` to audit the proofs.
This proves local factors and coefficient prefixes. The subsequent tame/wild
backends compute conductor/sign formulas and use the explicitly assumed
geometric compatibility to supply analytic certificate evidence.
See [the additive reduction notes](docs/ADDITIVE_REDUCTION.md).

The fixture now adds [1,000 further reference curves](data/lmfdb-1000-additional.json)
from a pinned snapshot of LMFDB's source data; all 1,100 labels are distinct and
kernel-checked. Provenance, schema, license and the 300-record direct-API
cross-check are in [data/lmfdb/README.md](data/lmfdb/README.md).

The bad-prime cap is removed through a proved linear root search. Expanded
additive arithmetic replay checks 532 of 580 selected models; 48 remain
inconclusive under the sufficient minimality criteria. Separately,
`lake exe negative-certificates --check` checks 229 exact rank-at-least-one
certificates. These are lower bounds, not exact rank-one results, and do not
populate the exact-rank cache. Geometric Tate/Ogg/Halberstadt compatibility
remains assumed in the strengthened general-modularity package. The 48 minimality gaps, central vanishing for 389.a1, and first-derivative
separation for 5077.a1 remain open. The first-derivative backend now proves exact
rank one for the other 228 negative-sign curves.

Use `lake exe certify-batch --seal-cache` to validate saved source hashes and
rebuild the known cache proof without rerunning candidate search. The combined
soundness proof composes checked entries instead of making one large case split.
See [EXPANDED_BACKEND.md](docs/EXPANDED_BACKEND.md).

General modularity is authorized for every E/Q, including additive reduction;
the existence axiom already covered all nonsingular equations. The earlier semistable
restriction belonged to the available arithmetic formulas, not the scope of
modularity; tame and wild additive formulas are now implemented too. [General certification](docs/GENERAL_MODULARITY.md) now
proves that continuation and analytic rank are independent of the chosen modular
realization, and accepts proof-carrying conductor/sign compatibility for any
curve. Executable-to-formula arithmetic correctness is proved independently;
database values do not substitute for those proofs or geometric compatibility.

The tame additive conductor/root-number backend is documented in
[docs/TAME_ARITHMETIC.md](docs/TAME_ARITHMETIC.md). Its executable-to-formula
proofs are axiom-free apart from standard foundations; identifying the formulas
with the modular level/sign is explicit in the authorized general-modularity
assumption. The subsequent [wild additive backend](docs/WILD_ARITHMETIC.md) handles reduction at 2 and 3 using checked Tate transcripts and Halberstadt tables.

## SQL expansion and conductor timing

The [SQL benchmark workflow](docs/SQL_BENCHMARK.md) downloads 10,000 further
curves from LMFDB's read-only mirror, excluding the existing 1,100 labels.
`conductor-certificates` keeps numerical computation and proof construction in
Lean; `scripts/benchmark_conductors.py` checks every available component and
records production, kernel build and warm validation times per conductor.
The 23-curve local smoke test passed with 180 concrete component audits.
The 10,000 additional SQL curves have been downloaded and verified against
their raw snapshot and provenance. The full conductor campaign is running;
its checkpointed reports distinguish completed timings from pending work.

## Local certificate command

The Python/PostgreSQL registry and browser volunteer application have been
retired. Their source is preserved in Git baseline `fcdc4f2`; local database and
signing-key state have not been deleted. The supported interface is now Lean's
`certify_ec` command: supply exact JSON or typed Lean witness data, compile once,
and import the resulting `.olean` theorem. No search is performed by default.
See [CERTIFY_EC.md](docs/CERTIFY_EC.md) for local examples and build instructions.

The Python files under `scripts/` remain optional database-download and benchmark
tools. They are not part of certificate validation. `make check` runs Ruff and
ty; `make test` runs the remaining snapshot/benchmark plumbing tests.
