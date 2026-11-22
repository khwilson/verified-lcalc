# Verify local elliptic-curve data in Lean

`certify_ec` is a Lean command. It checks the supported facts and witnesses present in the supplied data,
then declares ordinary definitions and theorems. It never invokes
witness search, a numerical producer, Python, a web service, or LMFDB. The
mathematical algorithms remain the existing proof-backed Lean implementation.

The old Python registry, browser volunteer application, service dependencies,
and generated batch certificate corpora/installers are removed. Git baseline `fcdc4f2` preserves their source. Existing ignored
local state and database volumes were not deleted; stop any old API/worker
processes yourself. The remaining Python scripts only download/benchmark data.

## Three input forms

For prime coefficients and integral-point membership without an analytic-rank
witness, see [arithmetic data certificates](#arithmetic-data-certificates) below.

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
bounds, minimality factors and local Tate transcripts. Malformed supported
fields are rejected; unrelated metadata is reported as unverified. File fixtures
are in `data/witnesses/`.
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

Both Lake configurations use the same pinned dependencies and caches. The
certificate examples and the LMFDB test fixtures list their required JSON
files as Lake inputs. Rebuilding with Lake after an edit rechecks the affected
certificates before a consumer imports them. Missing or renamed required files
fail the build.

In your own package, declare each required witness as an `input_file` target
and include its package target key in the certificate library's `needs` array,
for example ``needs := #[`@/witness]``. Lean reads the JSON during elaboration,
and Lake uses the declared file dependencies to decide when to repeat it.

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

## Arithmetic data certificates

Exact equation invariants and additional LMFDB fields are also optional witness
fields in this same command. See [LMFDB_INVARIANTS.md](LMFDB_INVARIANTS.md) for
their JSON names, generated theorems, and prerequisite evidence. In particular,
minimal discriminant and complete bad-prime claims require checked minimality;
conductor/global-root identification retains the documented temporary axiom.

`certify_ec` checks supplied prime coefficients and affine integer points
independently of the analytic-rank command:

```lean
module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

certify_ec MyData from
  { equation := ⟨0, 0, 1, -1, 0⟩,
    primeCoefficients := some [(2, -2), (37, -1)],
    integralCoordinates := some [(0, 0), (6, 14), (6, -15)] }

example : (MyData.curve.baseChange ℚ).LFunction 37 = -1 :=
  MyData.ap_correct 37 (-1) (by decide +kernel)

example : MyData.point ⟨0, by decide⟩ ∈ MyData.curve.integralPoints :=
  MyData.point_integral _
```

The same `from_json` and `from_json_string` input forms accept partial data,
with no schema or empty sections required:

```json
{
  "ainvs": [0, 0, 1, -1, 0],
  "ap": [[2, -2], [37, -1]],
  "integral_points": [[0, 0], [6, 14], [6, -15]],
  "lmfdb_label": "37.a1"
}
```

Fields are checked independently. `ap` carries explicit prime/value pairs;
LMFDB's `aplist` is also supported and is paired with the initial primes in
increasing order. The checker proves primality, a sufficient local minimality
condition, and equality with the existing finite-field trace. Its soundness
theorem identifies each value with the actual curve's `LFunction p`, including
bad primes. A failed supported check rejects the command and rolls back all
its declarations; an unsupported local minimality case is not certified.

`integral_points` contains integer `(x,y)` pairs. Each checked pair yields
membership in TauCeti's `integralPoints` for the supplied equation.
LMFDB's `xcoord_integral_points` also exports an exact finite y-fiber for each
listed x. The decoder produces one candidate y per x by completing the square.
The checker proves its equation and uses Weierstrass negation to recover the
whole fiber.

For each index `i` into `Name.integral_fiber_roots`, the equivalence
`Name.integral_y_fiber_complete i y` says that `y` belongs to
`Name.integral_y_fiber i` exactly when it satisfies the supplied equation at
that x. A double root counts once in the fiber. The original coordinate list
keeps its indexing, including repeated roots. Direct Lean input can supply the
same root witnesses in the optional `integralFiberRoots` field.

These fibers certify completeness only at the listed x-values. An empty list
checks zero fibers. The theorem gives no global integral-point count or
algebraic-rank bound.

LMFDB `gens` and `torsion_generators` accept exact weighted triples `[a,b,c]`
with `c ≠ 0` and decode to `(a/c², b/c³)` in ℚ. The corresponding direct
Lean fields `generatorCoordinates` and `torsionGeneratorCoordinates` take
exact affine pairs. Each supplied list exports `coordinates`, `points_on_curve`
and `point i` under `Name.generators` or `Name.torsion_generators`. These establish
membership on the rational curve.

To check individual torsion orders, supply the project-specific JSON field
`torsion_generator_orders` or the Lean field `torsionGeneratorOrders`.
Supply one claimed order per torsion coordinate pair in list order. Orders
from 1 to 256 are accepted for checking. The command exports
`Name.torsion_generators.exact_order i` for the corresponding affine point as
a theorem about Mathlib’s `addOrderOf`. An incorrect order, mismatched list
length, or missing coordinate list rejects the whole certificate. The
default when no orders are supplied is membership checking alone.
With a verified `torsion_bound` and the matching exact order of the first
torsion point, the LMFDB `torsion` claim certifies the cardinality of the
full rational torsion subgroup. Supply the cyclic `torsion_structure` as
`[n]` for a nontrivial group of order `n`. The structure theorem gives an
additive equivalence from `ZMod n` sending 1 to that first point. The trivial
group uses `[]` and the identity point. If the verified divisor is larger
than the claimed order, the cyclic certificate requires tighter evidence.
Invariant factors must be greater than one and each must divide every later
factor. Their product must agree with the claimed cardinality and divide the
verified upper divisor when those claims are supplied. Each checked point
order must divide the last factor, or one for the empty list.
Generation and independence require separate evidence.

The same `certify_ec` command establishes stronger facts when
`infiniteOrderPoints` or `independentPoints` is supplied in the witness.
The latter uses a `with_independence` proof clause. See
[ALGEBRAIC_RANK.md](ALGEBRAIC_RANK.md) and `CertifiedCurves.Direct`.

Direct Lean data uses the same optional-facts record:

```lean
certify_ec JustCoefficients from
  { equation := ⟨0, 0, 1, -1, 0⟩, primeCoefficients := some [(2, -2)] }

certify_ec Combined from
  { equation := Curve37.curve, primeCoefficients := some [(37, -1)],
    integralCoordinates := some [(0, 0)],
    derivativeResult := some Curve37.result,
    minimality := some Curve37.minimality,
    localData := some Curve37.localData }
```

The combined example assumes `import CertifiedCurves.Json`. There is one
aggregate input type, `VerifiedLcalc.EllipticWitness`: a required
`equation : WeierstrassCurve ℤ` and optional `primeCoefficients`,
`integralCoordinates`, `centralResult`, `derivativeResult`, `minimality`, and
`localData`, plus point-index lists `infiniteOrderPoints` and `independentPoints`.
All optional fields default to `none`. `some []` records an
explicitly supplied empty list; it does not assert completeness. JSON omission
or `null` represents absent arithmetic lists. Complete rank-witness JSON can
carry the same arithmetic fields, or appear under the legacy `analytic_witness`
key; both decode into this same flat record.

`EllipticWitness.central` and `.derivative` remain convenience functions that
populate the record. At most one numerical rank candidate can be supplied.
Numerical payloads are checked even without arithmetic witnesses, but an
analytic-rank theorem requires checked minimality and local data. Those two
components are also checked independently when supplied alone.
All inputs use one pipeline. The command verifies every supplied supported
witness and checks that its equations agree. It reports other JSON metadata
without emitting claims about it. In particular, a plain `rank` or
`analytic_rank` value is never converted into a theorem. Complete rank witnesses
retain their existing exact-format checks and modularity assumption.

Arithmetic JSON integers may be integer literals or canonical decimal strings,
with a 512-character bound. The profile permits 256 coefficients at primes up
to 10,000, up to 4,096 supplied coordinate pairs and 4,096 x-values, and at most
8,192 resulting coordinate pairs. The payload cap is 2 MiB.

`Name.witness` stores the common record; `Name.supplied` is an alias. Arithmetic
facts are exported as `ap_correct`, `points_on_curve`, `point` and `point_integral`, together with
`prime_coefficients_valid`, `integral_coordinates_valid`, `curve_isElliptic`,
and `nonsingular`. Arithmetic and analytic declarations share the same
`Name` namespace and equation. Arithmetic facts use only standard Lean axioms;
analytic-rank facts retain the explicit modularity assumption.

`CertifiedCurves.Data` contains two small examples with stored data for
[11.a1](https://www.lmfdb.org/EllipticCurve/Q/data/11.a1) and
[37.a1](https://www.lmfdb.org/EllipticCurve/Q/data/37.a1), with provenance in
`data/curve-data/provenance.json`. Lake tracks that directory as an explicit
input. Import `CertifiedCurves.Data` to reuse the checked results; see
`tests/consumers/CertifiedECDataConsumer.lean`.

## Analytic-rank declarations and trust

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
