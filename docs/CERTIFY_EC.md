# Verify local elliptic-curve data in Lean

`certify_ec` is a Lean command. It checks supplied numerical and arithmetic
witnesses, then declares ordinary definitions and theorems. It never invokes
witness search, a numerical producer, Python, a web service, or LMFDB. The
mathematical algorithms remain the existing proof-backed Lean implementation.

The old Python registry, browser volunteer application, service dependencies,
and generated batch certificate corpora/installers are removed. Git baseline `fcdc4f2` preserves their source. Existing ignored
local state and database volumes were not deleted; stop any old API/worker
processes yourself. The remaining Python scripts only download/benchmark data.

## Three input forms

```lean
module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

certify_ec MyCurve from_json "witness.json"
```

A JSON path is relative to the containing Lean file. The existing exact
`lcalc.ec-rank.v1` format is accepted: canonical decimal strings for integers,
`"numerator/denominator"` strings for rationals, explicit coefficients, numerical
bounds, minimality factors and local Tate transcripts. Malformed, extra or
unsupported fields are rejected. File fixtures are in `data/witnesses/`.
Rank-zero and rank-one witnesses are supported; numerical near-zero observations
do not become exact higher-rank claims.

The JSON profile permits rational strings up to 16,384 characters, with at most
8,192 characters per decimal component. Ordinary integer fields retain their
512-character cap, and the complete payload retains its 2 MiB cap. These are
data-format limits, not numerical precision assumptions; exact tail fractions
can exceed 1,024 characters even at 32 terms and 53 bits. Every accepted witness
still undergoes the same kernel checks.

For inline JSON use:

```lean
certify_ec MyCurve from_json_string r#"{ ...complete witness... }"#
```

The ellipsis above is explanatory, not valid witness data. A complete working
example is `examples/certify_ec/CertifiedCurves/Inline.lean`.

For supplied Lean data use an `EllipticWitness` expression:

```lean
certify_ec MyCurve from
  VerifiedLcalc.EllipticWitness.central result minimality localData

-- Or, for a first-derivative witness:
certify_ec AnotherCurve from
  VerifiedLcalc.EllipticWitness.derivative result minimality localData
```

Here `result`, `minimality`, and `localData` stand for supplied definitions or
literal structures, not search instructions. See `CertifiedCurves/Direct.lean`
for a complete literal example with no JSON input. Direct expressions must be closed supplied data and may use
existing transparent definitions. The command reduces the outer witness
constructor and verifies all resulting data. It does not automatically fill in
missing coefficients, precision, transcripts, or bounds.

## Import checked theorems

Build the examples and their compiled certificates from the project root.
`make certificates` builds them; `make test-certificates` also runs the command
regressions and the import-only consumer. The equivalent individual commands are:

```sh
lake -f lakefile.certificates.lean build CertifiedCurves
lake -f lakefile.certificates.lean env lean tests/consumers/CertifiedECConsumer.lean
lake -f lakefile.certificates.lean env lean tests/CertifyEC.lean
```

The alternative Lake configuration reuses the same pinned mathlib and existing
build caches. It declares `data/witnesses` as a Lake input target, so editing JSON
invalidates the certificate library. **Plain Lean file reads do not themselves
register Lake dependencies.** In your own package, track JSON with `input_file`
or `input_dir` plus the certificate library's `extraDepTargets`, or embed the
witness in the Lean source. Otherwise force source recompilation after edits.

After compiling, another file simply imports the module:

```lean
import CertifiedCurves.Json

open VerifiedLcalc VerifiedLcalc.Modularity

theorem rank_of_curve37 :
    analyticOrderAt (modularWitness Curve37.curve Curve37.nonsingular).formL
      (1 : ℂ) = 1 :=
  Curve37.analytic_rank
```

This consumer runs no certificate command, JSON parser, numerical search or
kernel reduction of the original witness checks. It imports the already compiled
proof. The `.olean` files live under `.lake/build/lib/lean/CertifiedCurves/`.
Distribute source and the exact Lean/mathlib/library environment with artifacts;
`.olean` imports require compatible versions and trust in the artifact producer.
A checksum or Git commit identifies content; it is not independent evidence of
kernel validation. Recipients can rebuild source if they want to check it locally.

## Generated declarations and trust

For prefix `MyCurve` the command exports:

- `witness`, `result`, `minimality`, `localData`, and `curve`;
- `witness_eq`, binding the elaborated fields back to the supplied Lean witness;
- `nonsingular`, `minimality_valid`, `local_data_valid`;
- `conductor_valid`, `root_number_valid`, `payload_correct`, `excludes_zero`;
- `analytic_rank`, `curve_analytic_rank`, and proof-carrying `certifiedRank`.

The JSON decoder and syntax reification are untrusted data plumbing. The theorem
is about the explicit equation and numbers actually represented in Lean; it is
not a theorem about an external database label. The decoder does not certify
JSON provenance. Every mathematical assertion is checked using ordinary proof
terms and `decide +kernel`. No `native_decide` or native verification axiom is
used. A failure rolls back the command's declarations, rather than leaving a
partially admitted certificate in the environment.

The command audits every generated proof. Finite component proofs may use only
standard Lean/mathlib axioms. Analytic-rank proofs may additionally use the single
user-authorized `VerifiedLcalc.Assumptions.ellipticModularity` package, including
its documented arithmetic compatibility assumptions. They remain conditional
on that package. Successful elaboration is logged only after all checks pass.

For throughput, place multiple `certify_ec` commands in one module so they share
one checker import. See [the performance measurements](CERTIFY_EC_PERFORMANCE.md)
for command, fresh-process and batched costs.

Metaprogramming changes the interface, not the fundamental initial checking cost.
`lake build` reuses completed compiled certificates; `lake env lean FILE.lean`
explicitly replays the commands in that source file.

## Validation of the initial implementation

The command examples compile for a direct Lean witness, inline JSON, and JSON
files at conductors 11, 37 and 112. The tests reject altered coefficients, tails,
conductors, minimality witnesses and malformed/unsupported JSON, check rollback,
and audit all component theorem axioms. A separate compiled-module consumer
proves the rank-one statement and evaluates `certifiedRank.val` to `1`.

The existing full default Lake build, cubic source replay, cubic import-only
consumer and `Audit.lean` pass. Ruff, formatting and ty pass; the remaining eight
Python snapshot/plumbing tests pass. This does not certify every LMFDB entry or
remove the documented modularity assumptions.

## Explicit higher-rank hypotheses

The current command proves exact rank zero or one using nonvanishing; those
results are not rounded rank observations. For higher-order smallness data, use
`Assumptions.CurvePrecisionClaim` and its indexed `Hypotheses` proposition in
`VerifiedLcalc/Assumptions/Precision.lean`. These record the exact equation,
precision policy, derivative prefix and assumed nonzero gap. Their conditional
lower-bound/rank theorems retain the separation assumption as an argument.
Actual higher derivative enclosures are still required and are not supplied by
the assumption record. See [NUMERICAL_RANK.md](NUMERICAL_RANK.md) and the opt-in
[explicit assumptions](../VerifiedLcalc/Assumptions/README.md).

The reusable-theorem extraction plan is in [TAUCETI_ROADMAP.md](TAUCETI_ROADMAP.md),
with separate arithmetic and analytic roadmaps. Certificate metadata and
metaprogramming stay in this project; mathematical replacements should be
upstreamed independently, with their own proof and axiom audits.
