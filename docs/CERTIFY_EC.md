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
Choose the import for the value you are constructing or reading.

```lean
-- Construct an input record.
import VerifiedLcalc.Certificate.Witnesses.EllipticWitness
```

For the checked output type, import
`VerifiedLcalc.Certificate.Witnesses.EllipticCertificate`. For just the
Mordell–Weil rank bounds, import
`VerifiedLcalc.Certificate.Witnesses.Algebraic`.
The `VerifiedLcalc.Certificate.Witnesses` umbrella makes all ordinary structures available.
The raw input contains optional supplied claims; checked rank bounds are part of
`IntegralCurveProofs`.
The [import regression](../tests/consumers/RawWitnessImports.lean) checks
the raw input’s dependency boundary in Lean.

The [module map](CERTIFICATE_CONTRACT_LAYOUT.md) lists the structures by
subject. The witness source is organized into `FinitePrimes`,
`Analytic`, `Algebraic`, and `Invariants`, with shared supplied-field records
under `InputData` and the two aggregate records at the witness root. The
ordinary umbrella excludes assumption-dependent declarations; import
`Certificate.Witnesses.Assumptions` when those declarations are needed.

The checked certificate’s `equationFacts` and `rational` fields hold exact invariants. The `algebraic`
field holds membership of supplied points, complete
integral y-fibers above specified x-coordinates, the complete integral-point
set when exhaustive abscissa support is supplied, individual point orders, an
independent family, and proved rank bounds for the actual rational point group.
`certificate.algebraic.rankBounds` contains the checked interval, while
`certificate.algebraic.rank` is present only when the interval proves an exact
rank. `certificate.algebraic.generatorCount` reads the size of the checked
rational point family. If the input supplies `ngens`, the command verifies
that it equals this size. The
`arithmetic` field
exposes finite reduction facts and separate conditional results. To use a conditional arithmetic result, supply
an explicit `ArithmeticModularRealization` of the equation. The `analytic`
field keeps checked numerical payloads and separately gives enclosures and
ranks conditional on an explicit realization. The `torsion` field can carry a
verified positive multiple of the full subgroup order, a consistent supplied
count, and an exact cardinality when determined.

`certificate.torsion` is a single `TorsionWitness`. Its `generators` field
holds the submitted family of rational points in order. When `orders` is
present, applying it to an index gives the positive order and its proof for
that point. The `generation` field proves that these points generate the full
rational torsion subgroup. The `presentation` field identifies that subgroup
with a product of cyclic groups and names the submitted point corresponding
to each standard generator. For a presentation with factors `[2, 4]`, two
generators describe all eight elements. For trivial torsion the factor family
is empty. Given an exact group order, `primeSupport` records its distinct prime
divisors and a proof of completeness.

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

## Check an ordinary p-adic regulator ball at rank zero

Submit one grouped `padic_regulator` object in JSON, for example
`{"p":7,"prec":20,"val":0,"unit":"1"}`, or use `EllipticWitness.padicRegulator`
in Lean. The absolute precision `prec` and valuation `val` are signed
integers. A nonzero ball needs `val < prec`. The unit is the least
nonnegative representative modulo `p^(prec - val)` and must be prime to
`p`. Exact JSON integers and canonical decimal strings are accepted.

The command checks that the equation has smooth ordinary reduction at
`p`. An independent exact Mordell–Weil rank-zero proof for the equation,
supplied through `with_proofs`, lets the command check a ball about the
empty height determinant, which equals one. The normalized data then have
`val = 0`, `unit = 1`, and `prec > 0`. The proof of containment in the
reported ball is available through `Name.certificate.analytic.padicRegulator`.
Missing exact rank evidence or a positive rank leaves the regulator
unverified.

The rank-zero JSON example is a finite-precision encoding of the value
displayed by LMFDB. The display reads a stored class row for positive rank
and LMFDB curve number 1. Within the p-adic object, `lmfdb_iso` is catalogue metadata.
[LMFDB p-adic regulator renderer](https://github.com/LMFDB/lmfdb/blob/a0c7fdc3b7ab1d7f11d324242e4707896c5b3529/lmfdb/elliptic_curves/elliptic_curve.py#L775-L792)

## Check Cremona labels in singleton cases

Submit `Ciso` and `Clabel` as exact strings and `Cnumber` as an exact natural
number. The matching Lean fields are `cremonaIso`, `cremonaLabel`, and
`cremonaNumber`. Supply `IntegralCurveProofs.cremonaSingleton` through
`with_proofs`. It carries the actual algorithmic conductor norm and a proof
that it is in the published range, from 1 through 500000.

Attach `onlyClass` for `Ciso`, `onlyCurve` for `Cnumber`, or both for `Clabel`.
These are exhaustive proofs about the conductor's rational isogeny classes
and the subject's rational isomorphism classes, respectively. The resulting
proofs are available through `Name.certificate.cremonaCatalogue`. Other
historical orderings remain unverified.
[LMFDB convention](https://www.lmfdb.org/knowledge/show/ec.q.cremona_label)
· [Published Cremona tables](https://github.com/JohnCremona/ecdata/tree/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allcurves)

## Check the LMFDB catalogue indices and labels

Submit any of `lmfdb_number`, `iso_nlabel`, `lmfdb_iso`, and `lmfdb_label`
as exact JSON fields, or use the corresponding Lean fields `lmfdbNumber`,
`isoNlabel`, `lmfdbIso`, and `lmfdbLabel`.

- `lmfdb_number` uses `IntegralCurveProofs.isogenyClass` with complete
  reduced minimal ordering. It is one plus the subject's position in that order.
- `iso_nlabel` and `lmfdb_iso` use `IntegralCurveProofs.conductorClassRoster`.
  The roster covers all rational isogeny classes of the subject's intrinsic
  algorithmic conductor norm. Strict lexicographic order uses the actual rational
  L-function coefficients. A rational isogeny places the subject in the selected
  class.
- `lmfdb_label` uses both proofs. Submit the full label alone or alongside the
  individual fields.

The conductor is written in decimal, the zero-based class index in base 26
(`0 ↦ a`, `25 ↦ z`, `26 ↦ ba`), and the one-based curve number in decimal.
Each checked value and its proof are available under
`Name.certificate.lmfdbCatalogue`. A field with missing order evidence remains
unverified. [LMFDB label convention](https://www.lmfdb.org/knowledge/show/ec.q.lmfdb_label)

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
`infiniteOrderPoints`, `independentPoints`, or `independentGeneratorPoints` is supplied in the witness.
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
`localData`, plus point-index lists `infiniteOrderPoints`, `independentPoints`, and `independentGeneratorPoints`.
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

## Exceptional primes and finite adelic generators

Submit `nonmax_primes` and `nonmax_rad` with
`IntegralCurveProofs.nonmaxSupport`. The proof supplies geometric non-CM and
an actual Tate-module image at every prime. The command compares the submitted
primes as a finite set, rejects repetitions and composites, and checks the
radical by multiplying over the proved support. The results are available
through `Name.certificate.nonmaxPrimes`.

For `modell_image`, submit the label and its `prime` from the local row.
Attach `IntegralCurveProofs.modPrimeImage` with an exact image on the full
geometric prime torsion and a conjugacy proof against the supported Sutherland
label. The result is available at `Name.certificate.modPrimeImage`.
For `modell_images`, attach `IntegralCurveProofs.modPrimeImages` with one
checked image per label in report order. The optional coverage field proves
that the list accounts for exactly the non-surjective residual primes, given
geometric non-CM and all-prime image evidence. Use the list's membership
theorem `ModPrimeImageListFact.exists_of_mem_labels` to retrieve a verified
entry from `Name.certificate.modPrimeImages`.

For `adelic_level`, `adelic_index`, or `adelic_genus`, provide
`IntegralCurveProofs.adelicImage` with an exact simultaneous image on all Tate
modules and the corresponding proof. The level is the least positive modulus
whose reduction kernel lies in the image. The index is the number of cosets
in the integral adelic group. For genus, supply the finite CW structure and
Euler characteristic of the compactified effective quotient of the
determinant-one integral pullback. The command projects these proofs at
`Name.certificate.adelicImage`.

A prime-zero `adelic_image` of the form `N.i.g.?` compares its level,
index and genus with all three proved invariants. The formatting equality is
available in the certificate's `partialLabel` field. A class identifier in the
suffix needs an independent conjugacy-class comparison and remains unverified.

For `adelic_gens`, submit the generator array from the LMFDB prime-zero row
with the curve equation and either `adelic_level` or `adelic_image`. Use
`IntegralCurveProofs.adelicGenerators` to give the invertible matrices and
the proof that they generate the complete image on the geometric torsion at
the stated modulus. The typed matrices and image evidence are available
through `Name.certificate.adelicGenerators`.
[Field semantics and source format](LMFDB_INVARIANTS.md#checks-implemented)

## Canonical heights and a torsion growth field

Use the LMFDB `ec_mwbsd` fields `gens` and `heights` together. The height
array accepts exact decimal numbers, decimal strings, and Sage real-literal
objects. An optional `"heights_evidence":{"errors":[...]}` supplies explicit
absolute error radii in generator order. Attach `IntegralCurveProofs.canonicalHeights`
with the indexed Lean proofs for those points, centers, and optional radii.
`Name.certificate.algebraic.heights` exports the enclosures for the checked
`gens` points. The submitted digits alone supply no error estimate. The height
is the BSD normalization, the limit of the logarithmic x-coordinate height of
the doubled points divided by the corresponding powers of four.

Place one native `ec_torsion_growth` row under the JSON key `torsion_growth`.
For example, the row for `y² = x³ + x` over ℚ(i) has
`"torsion_growth":{"field":[1,0,1],"degree":2,"torsion":[2,2]}`.
`field` gives integral coefficients in ascending order. The command proves
the dimension of the root-adjoining algebra from the submitted degree and
requires `IntegralCurveProofs.torsionGrowthField` to prove irreducibility and
give a new finite-order point for this curve. Construct the proof with
`TorsionGrowthFieldClaim.polynomial` for the same coefficient vector.
`Name.certificate.torsionGrowthField` exports the field, the degree proof,
and the strict growth proof. Full extension torsion invariant factors and
primitivity over proper subfields require additional evidence.

## Complex period area and Faltings data

Attach `IntegralCurveProofs.periodGeometry` with `with_proofs`. The corresponding
`Name.certificate.periodGeometry` contains global minimality of the input equation
and any supplied proofs for the three enclosures and the exact class ratio. The
enclosures can be supplied independently. The class ratio carries a complete rational
isogeny class model, a proof of global minimality for each representative, an
index attaining the greatest area, and an exact equality with the input area times
the positive integer ratio.

The exact JSON keys are `area`, `faltings_height`, `stable_faltings_height`
and `faltings_ratio`. To require a particular rational radius for a decimal,
include `area_evidence`, `faltings_height_evidence`, or
`stable_faltings_height_evidence` with an `error` field. The checker compares
each submitted center and any submitted radius with the attached enclosure.
For a submitted value with matching evidence the command emits a theorem
such as `Name.area` about that report. With the JSON key omitted, a standalone
proof supplied in the Lean attachment still appears in
`Name.certificate.periodGeometry`. In that case there is no theorem about a
catalogue value. A decimal alone stays a report. The checker leaves `faltings_index` as catalogue
ordering metadata.
