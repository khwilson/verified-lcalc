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

## Attach an exact proof in Lean

An ordinary Lean caller can build a `DiscriminantWitness R` over a commutative
ring. The record carries the equation, the proposed value, and its proof.

```lean
open VerifiedLcalc

def exampleDelta : DiscriminantWitness ℤ where
  curve := ⟨0, 0, 1, -1, 0⟩
  discriminant := 37
  discriminant_eq := by decide +kernel

certify_ec E from { equation := exampleDelta.curve }
  with_proofs exampleDelta.toProofs

example : E.discriminant_witness.curve.Δ = 37 :=
  E.discriminant_witness.discriminant_eq
```

The attachment is an `EllipticProofs` record indexed by the exact integral
equation. Its optional discriminant field carries a value with a proof about
that equation. It can also be constructed as
`{ discriminant := some ⟨d, hd⟩ } : EllipticProofs curve`.
A raw `discriminant` claim and the supplied value must agree when both are
present. The certifier audits the proof dependencies and rejects a mismatched
attachment atomically. A successful raw Lean or JSON claim also exports
`Name.discriminant_witness`. The checked b-invariants, c-invariants, and
discriminant are available together as `Name.checked_facts` when at least one
is supplied. Both the raw data and the attachment can supply entries:

```lean
certify_ec WithTuples from
  { equation := exampleDelta.curve, bInvariants := some (0, -2, 1, -1) }
  with_proofs
    { exampleDelta.toProofs with cInvariants := some ⟨(48, -216), by decide +kernel⟩ }
```

The same attachment works after `from_json` and `from_json_string`.
Use `with_independence` after `with_proofs` when supplying both. Additional
proof-carrying facts can use the same index. For example, a downstream Lean
record can carry an `EllipticProofs curve` and
`c₄Value : {a : R // curve.c₄ = a}` side by side, and pass its
first field to the current command.

## Use the checked certificate

Each successful command exports `Name.certificate` indexed by its integral
Weierstrass equation. Its input and output structures are declared in
[`Certificate/Witnesses/`](../VerifiedLcalc/Certificate/Witnesses).
Import `VerifiedLcalc.Certificate.Witnesses` to use the structures.
The [module map](CERTIFICATE_CONTRACT_LAYOUT.md) lists their source files.
These modules use Mathlib and TauCeti objects where
available, with local definitions limited to specific certificate encodings
that upstream does not provide. Proof-only dependencies remain ordinary imports,
and public re-exports are reserved for declarations in signatures and the
intentional umbrella API. The compiler-backed import boundary is checked by
[`tests/consumers/CertificateContracts.lean`](../tests/consumers/CertificateContracts.lean).
Its `equationFacts` and `rational` fields hold exact invariants. The `algebraic`
field holds membership of supplied points, complete
integral y-fibers above specified x-coordinates, the complete integral-point
set when exhaustive abscissa support is supplied, individual point orders, an
independent family, and proved rank bounds for the actual rational point group.
`certificate.algebraic.rankBounds` contains the checked interval, while
`certificate.algebraic.rank` is present only when the interval proves an exact
rank. `certificate.algebraic.generatorCount` proves that `ngens` is the length
of the supplied `gens` list; it does not claim that the list is a basis. The
`arithmetic` field
exposes finite reduction facts and separate conditional results. To use a conditional arithmetic result, supply
an explicit `ArithmeticModularRealization` of the equation. The `analytic`
field keeps checked numerical payloads and separately gives enclosures and
ranks conditional on an explicit realization. The `torsion` field can carry a
verified positive multiple of the full subgroup order, a consistent supplied
count, and an exact cardinality when determined.

The `torsion.cyclicStructure` projection gives the checked cyclic factors,
order, and rational generator. For factors `[2, n]`,
`torsion.twoFactorStructure` holds the actual `AddEquiv` from
`ZMod 2 × ZMod n` onto Mathlib's full torsion subgroup, with proofs that the
coordinate generators map to the supplied rational points. When an exact full
torsion order is proved, `torsion.primeSupport` gives the distinct prime list,
its nodup proof, and a theorem characterizing its members by primality and
divisibility of the subgroup cardinality.

The `rational.abcQuality` projection holds the exact reported value and error,
the validated factorization, and the certified bound on the actual quality.

For example, the following reads an invariant from a compiled certificate
using its exact proof. The default handles a missing value using the equation.

```lean
example : E.curve.Δ =
    (E.certificate.equationFacts.discriminant.getD ⟨E.curve.Δ, rfl⟩).val :=
  (E.certificate.equationFacts.discriminant.getD ⟨E.curve.Δ, rfl⟩).property
```

Use `E.certificate.equationFacts` as the `with_proofs` attachment when the
next certificate checks the same integral equation.

## Verify a supplied Mordell–Weil rank proof

Attach `IntegralCurveProofs W` with its `algebraicRank` field set to a checked
`AlgebraicRankBounds (W.baseChange ℚ)`. The same attachment can contain the
equation-level facts. Its lower and upper inequalities refer to
`Module.finrank ℤ (W.baseChange ℚ).toAffine.Point`. TauCeti's proved
Mordell–Weil instance supplies finite generation for every nonsingular
rational elliptic curve, so this is the natural-number rank of the actual
Mathlib point group.

With this evidence, `certify_ec` can verify JSON `rank_bounds: [lower, upper]`
and an exact algebraic `rank` claim. It exports `Name.algebraic_rank_bounds`
and `Name.algebraic_rank_witness`. A checked infinite-order point or independent
family can tighten the lower endpoint. A singleton after tightening also
exports `Name.algebraic_rank`. The exported interval can be wider than the supplied
proof interval. Reuse its typed witness as the `algebraicRank` field in a
later proof attachment over the same equation.

## Check a stored regulator

The `regulator` field accepts an exact JSON decimal, canonical decimal string,
or Sage real literal; its `prec` value is metadata and does not supply an error
bound. Optional `regulator_evidence.error` gives a nonnegative exact absolute
error as a decimal or rational value. With an
exact algebraic rank proof of zero, the checker uses TauCeti's rank-zero
regulator theorem to certify the enclosure in
`Name.certificate.algebraic.regulator`. An omitted error is accepted only when
the report is exactly one. A bad error or an enclosure disjoint from one rejects
the whole command. Without an exact zero-rank proof, the field remains
unverified; positive-rank regulators need a separate mathematical evaluator.

## Check a stored special value

The optional `special_value` is a leading Taylor coefficient
`L^{(r)}(1)/r!` in arithmetic normalization. The shared decoder accepts an
exact JSON decimal, canonical decimal string, or Sage `__RealLiteral__` data.
The `special_value_evidence.error` field must supply a nonnegative exact
rational (integer, fraction string, or numerator/denominator pair); the
precision tag is never treated as an error bound. The checker accepts a
report only when a checked central enclosure establishes order zero or a
checked first-derivative enclosure establishes order one, and verifies the
reported interval against that actual enclosure. The resulting proof is
available as `Name.certificate.analytic.specialValue` and applies to every
`ArithmeticModularRealization` of the same curve. Higher-order evaluators are
not supplied, so a higher-order report remains unverified.

An inline legacy analytic payload still uses `rank` for the numerical
candidate. With nested `analytic_witness`, a top-level algebraic claim can be
supplied separately. The explicit `algebraic_rank` key is also accepted.
An analytic-rank theorem and a generator basis each need their own evidence.
The compiled example uses TauCeti's worked two-descent for `y² = x³ - x + 1`.
The pinned LMFDB input row `92b1` / `92.a1` records rank `1`, bounds `[1,1]`,
one generator, and `[[1,1,1]]` in
[`curvedata-first-1200.txt`](../data/lmfdb/raw/curvedata-first-1200.txt#L275).
The separate `Partial` example deliberately weakens that interval to `[0,2]`.

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
checks zero fibers. They make no global count claim on their own.

For a complete integral-point count, add `integralXSupport` to the
`IntegralCurveProofs` attachment. Its `IntegralXSupport` proof must place
every affine integral solution's x-coordinate in the supplied support list.
The command checks that each support value occurs among the checked fiber
seeds. It unions their exact fibers into a finite set of distinct pairs, even
if the input repeats a seed or supplies both roots at an x-coordinate.
`Name.num_int_pts` proves the cardinality of the actual affine integral
point set. The command checks a supplied `num_int_pts` JSON claim or
`numIntegralPoints` Lean claim and derives the count when it is omitted.
The counted set is TauCeti's `curve.integralPoints`, with membership expressed
through the existing integral-coordinate characterization
([pinned definition](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Integral.lean#L101-L114)).
The reusable result is also available as
`Name.certificate.algebraic.completeIntegralPoints`; it includes the support,
finite coordinate set, completeness theorem, explicit finiteness of
`Name.curve.integralPoints`, and the `Nat.card` equality. Without support, a
raw count stays unverified, but a count below the number of distinct checked
points or seed-fiber solutions is rejected.

### Complete integral-point counts

`ec_curvedata.num_int_pts` supplies the claimed count and
`ec_mwbsd.xcoord_integral_points` supplies candidate x-values. In JSON, include
both fields and provide an equation-indexed support proof:

```lean
def pointProofs : IntegralCurveProofs curve :=
  { integralXSupport := some support }

certify_ec Counted from_json "curve.json" with_proofs pointProofs

example : Nat.card Counted.curve.integralPoints =
    Counted.integral_point_certificate.count := Counted.num_int_pts
```

Here `support` proves every affine integral solution's x-coordinate occurs in
the listed fibers; the result stores the exact distinct-point count. A complete
compiled example is `VerifiedLcalcTests.Fixtures.Curve27a3`; it proves the
count two using Fermat's theorem for cubes. The count-zero consumer uses a
separate congruence proof.

LMFDB `gens` and `torsion_generators` accept exact weighted triples `[a,b,c]`
with `c ≠ 0` and decode to `(a/c², b/c³)` in ℚ. The corresponding direct
Lean fields `generatorCoordinates` and `torsionGeneratorCoordinates` take
exact affine pairs. Each supplied list exports `coordinates`, `points_on_curve`
and `point i` under `Name.generators` or `Name.torsion_generators`. These establish
membership on the rational curve. The optional `ngens` claim
(`generatorCount` in Lean) verifies the length of the supplied `gens` list
and exports `Name.generators.count_valid`. A claim with no list remains
unverified.

The public generic order checker is `EllipticWitness.exactOrderCheckMul` with
soundness theorem `exactOrderCheckMul_sound`. It checks a nonzero claimed order,
the claimed power, and each proper power indexed by a prime divisor. Its
`@[to_additive]` API generates the established `exactOrderCheck` and
`exactOrderCheck_sound` names used for additive groups.

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
group uses `[]` and the identity point. If the verified bound is larger
than the claimed order, the cyclic certificate requires tighter evidence.
A structure `[2, n]` with positive even `n` requires two supplied points of
orders 2 and `n` in that order, and a verified divisor of `2 * n`. The
command checks that the first point lies outside the cyclic subgroup of the
second. The structure theorem gives an additive equivalence from
`ZMod 2 × ZMod n` sending the coordinate generators to the supplied points.
An order-2 point that is already a multiple of the second point fails this
check and rolls back the certificate.

The checked fixture for LMFDB 120.b4 has equation `[0,1,0,-20,0]`, two-factor
structure `[2,4]`, and point coordinates `(0,0)` and `(-2,6)`. Its compiled
consumer uses the stored equivalence directly and proves the full subgroup has
cardinality 8 and prime support `[2]`.

The optional native JSON field `torsion_primes` must list the distinct primes
in ascending order. The checker compares it with the canonical
`Nat.primeFactorsList` support. A bound on the torsion cardinality alone cannot
certify prime support; the command leaves it unverified until an exact
cardinality is established.

Invariant factors must be greater than one and each must divide every later
factor. Their product must agree with the claimed cardinality and divide the
verified divisibility bound when those claims are supplied. Each checked point
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

A native `analytic_rank` or Lean `catalogueAnalyticRank` is an optional
catalogue value to compare with an independently verified order. The command
exports `E.catalogue_rank` and `E.catalogue_analytic_rank` only after an actual
analytic payload establishes that same order. Both are indexed by the checked
curve and use an explicitly supplied arithmetic modular realization. A conflict
rolls back the whole command. Missing analytic evidence leaves the reference
value unverified. The algebraic `rank` column and the legacy rank-witness
format's payload selector have their existing meanings.

## A single degree-two rational isogeny edge

An `isogeny_edge` JSON object or Lean `isogenyEdge` specifies the target
equation and a claimed minimum degree. For degree two, either supply a checked
proof with `with_isogeny proof` or specify `kernel_x` as an exact rational
x-coordinate (Lean `kernelX`). The raw kernel form checks a point with y=0
on a source with a₁=a₃=0 and compares the exact Vélu quotient to the supplied
target. Use the proof attachment for other rational transports.

The command exports `E.degree_two_isogeny` indexed by both equations and
`E.isogeny_minimum_degree` about the degrees of all rational isogenies in
this direction. `E.certificate.isogeny` pairs the checked target with the
same typed edge. The exhibited map has a two-element cyclic rational kernel.
A source or target label supplied alongside the equations is provenance.
The fixture checks the edge 112.a2 → 112.a1 in the
[LMFDB 112.a class](https://www.lmfdb.org/EllipticCurve/Q/112/a/).
