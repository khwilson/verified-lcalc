# verified-lcalc

Lean 4 arithmetic, interval evaluation, and proof-producing metaprogramming for
elliptic-curve analytic ranks. Curves use Mathlib's `WeierstrassCurve ℤ` directly;
base change uses its ring-map API. There is no separate curve-equation data type.

`certify_ec` verifies supplied numerical and local-arithmetic witnesses and emits
ordinary named theorems. It accepts exact JSON files, inline JSON, or Lean data.
It performs no witness search by default. Compiling a certificate produces an
`.olean` module that other proofs can import without repeating its validation.

The same command also verifies supplied prime coefficients and integral-point
membership independently of analytic rank. It exports actual `LFunction p`
identities, including supported bad primes, and membership in TauCeti's
`integralPoints` set. See [the arithmetic-data interface](docs/CERTIFY_EC.md#arithmetic-data-certificates).

Exact rank zero follows from proved nonvanishing of the central value. Exact
rank one follows from sign-forced exact central vanishing and proved nonvanishing
of the first derivative. Both use rigorous coefficient identification, Mellin
formulas, interval rounding and tail bounds. The analytic claims currently
retain the explicit authorized general-modularity assumption, including the
documented conductor/root-number compatibility. Finite numerical checks are
independent of that assumption. No `native_decide` or tolerance-based exact zero
is accepted.

## Local use

Both Lake configurations use the published TauCeti `v4.37.0-rc1` tag at
`e0e414ce57522ba17560057ad0d7f2edab91bf0c`, Lean `v4.37.0-rc1`, and
Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`.
See [BUILD.md](docs/BUILD.md) for dependency and cache instructions.

```sh
make certificates
make test-certificates
```

These commands use `lakefile.certificates.lean`, which tracks JSON input changes
and builds the supplied examples. A certificate module looks like:

```lean
module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

certify_ec MyCurve from_json "witness.json"
```

All inputs use one `EllipticWitness` record with a `WeierstrassCurve ℤ` equation
and optional fact fields defaulting to `none`. The [witness directory](VerifiedLcalc/Certificate/Witnesses)
contains the input record, the checked `EllipticCertificate` exported as
`Name.certificate`, and their component structures. Components are grouped by
subject in `FinitePrimes`, `Analytic`, `Algebraic`, and `Invariants`.
Shared input records live in `InputData`. For complete rank candidates,
`EllipticWitness.central result minimality localData` and
`.derivative result minimality localData` populate this same record.
See [CERTIFY_EC.md](docs/CERTIFY_EC.md) for complete examples,
all three input forms, generated declarations, rollback and the trust boundary.

`certify_ec` also checks infinite-order requests in `infiniteOrderPoints` and
rank families in `independentPoints`. Supply a family's independence proof with
`with_independence` on the same command. See
[ALGEBRAIC_RANK.md](docs/ALGEBRAIC_RANK.md) for examples and the remaining
independence automation.

Stored j/discriminant invariants, bad-prime sets, coefficient prefixes, and
standalone conductor/root claims use that same interface. See
[LMFDB_INVARIANTS.md](docs/LMFDB_INVARIANTS.md) for supported fields, evidence
requirements, and the remaining cases and proof production work.

A consumer can simply write:

```lean
import CertifiedCurves.Json

#check Curve37.curve
#check Curve37.analytic_rank
```

Compatible Lean/library dependencies are needed to import compiled artifacts.
A file hash identifies an artifact; it does not independently attest kernel
execution. Recipients can rebuild the source to check it themselves.

## Mathematical backend and assumptions

The project retains proved local arithmetic, Euler coefficients, exponential and
logarithmic interval bounds, Mellin formulas and first-derivative enclosures.
The [wild arithmetic](docs/WILD_ARITHMETIC.md),
[first derivative](docs/FIRST_DERIVATIVE.md), and
[assumption boundary](docs/ASSUMPTIONS.md) documents describe their mathematical
meaning. Broader derivative evaluation and a complete lcalc translation remain
unfinished.

For numerical higher-rank observations, precision-small derivatives are separate
from exact vanishing. Explicit per-curve separation records bind the equation,
precision, derivative prefix and assumed nonzero gap. Conditional rank/lower-bound
theorems keep that hypothesis visible and require actual derivative enclosures;
exact rank also requires the next derivative to be nonzero. No blanket gap axiom
has been installed. See [NUMERICAL_RANK.md](docs/NUMERICAL_RANK.md) and
[precision assumptions](VerifiedLcalc/Assumptions/README.md).

The [Tau Ceti roadmap](docs/TAUCETI_ROADMAP.md) separates reusable upstream theory
from project-specific certificate machinery. The
[performance report](docs/CERTIFY_EC_PERFORMANCE.md) records kernel validation
timings and historical experiments. A [1,000-curve run](docs/CERTIFY_EC_DATASET_BENCHMARK.md)
produced 952 certificates in 915 seconds of active validation time, averaging
0.96 seconds per successful certificate in batches of 20. The other 48 inputs
hit insufficient minimality criteria.

## Development and historical data

```sh
make test-lean
uv sync --locked
make check
make test
```

`make test-lean` runs the [axiom audits](tests/audits) along with certificate
regressions. For an individual audit, build the relevant library modules and run
`lake env lean tests/audits/Audit.lean` from the repository root. The
[assumptions guide](VerifiedLcalc/Assumptions/README.md) explains the separate
modularity and low-rank BSD audits.

Ruff and ty cover the remaining Python download/benchmark plumbing. Mathematical
computation and certificate verification are in Lean.

The Python/PostgreSQL registry, browser volunteer app, generated Batch/
DerivativeBatch/ConductorRuns certificate corpora, generated cached-key tables,
and their installers have been retired. The old implementation and historical
1,100-curve results are preserved in Git baseline `fcdc4f2`; they are not a
preinstalled certificate cache in the current source tree. Old timing/provenance
reports and raw downloaded curve data remain historical evidence. Only small
local fixtures needed for the new command's tests are retained as witness inputs.
Local ignored service state and database volumes were not deleted.


The production/test layout is documented in [tests/README.md](tests/README.md).
Explicit assumptions are isolated in [Assumptions/README.md](VerifiedLcalc/Assumptions/README.md),
local reduction in [Tate/README.md](VerifiedLcalc/EllipticCurve/Tate/README.md),
and active numerical modules in [Numerics/README.md](VerifiedLcalc/Numerics/README.md).


The [file-by-file audit and applied cleanup queue](docs/ELLIPTIC_CURVE_FILE_AUDIT.md)
covers all 44 elliptic-curve source files. The earlier
[interface audit](docs/INTERFACE_REUSE_AUDIT.md) records direct
Mathlib/TauCeti reuse and remaining bridges. [TAUCETI_BACKLOG.md](docs/TAUCETI_BACKLOG.md)
contains the extracted, compiled upstream candidates and separate proof obligations.
