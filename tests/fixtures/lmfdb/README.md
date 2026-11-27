# LMFDB arithmetic CI cases

The ten LMFDB labels and exact values come from the vendored
[curvedata snapshot](../../../data/lmfdb/raw/curvedata-first-1200.txt).
The [source notes](../../../data/lmfdb/README.md) record the upstream commit and license.

Each JSON file copies the integral equation, rational j-invariant, discriminant sign,
absolute minimal discriminant, bad primes, and integral-point x-coordinates. The discriminant is the signed absolute
value. Multiplicities in the minimality witness come from the local discriminant
valuations. The fixtures include prime and composite conductors, both discriminant
signs, and j-invariants 0 and 1728. The 197.a1 and 288.a1 cases explicitly request
nonintegral and integral j-invariant certificates, respectively.

The conductor is copied from the snapshot. The global root number is the negative product of its
finite local root numbers. The 2-adic transcript for 112.a2 comes from
[the existing witness](../../../data/witnesses/112a2.json). The wild transcripts for 243.a1
and 288.a1 were computed with Lean's `wildData?` before being supplied to the verifier.

The [112.a2 joined LMFDB capture](https://www.lmfdb.org/EllipticCurve/Q/data/112.a2?_format=json)
records timestamp `2026-11-26T01:59:10.892609`. The captured response has SHA-256
`a7631a589136e92ffed788998da29e801cc6683dc8c87c0bb4d7f04913181171`.
The LMFDB Collaboration supplies these data under CC BY-SA.
[`112.a2-native.json`](112.a2-native.json) preserves the response bytes.
Its [provenance manifest](112.a2-native.provenance.json) records the curve,
class, prime and extension-field row keys across all eight tables. The native
capture contains 7 torsion-growth rows, one Iwasawa row and 19 p-adic rows
for the isogeny class, in addition to the five tables in
[`112.a2-joined.json`](112.a2-joined.json). The latter is the legacy selected
projection.

[`37.a1-trace-hash-source.json`](37.a1-trace-hash-source.json) contains the
equation and trace hash recorded on row 77 of the pinned
`curvedata-first-1200.txt` source snapshot, plus the conductor, minimality,
and local-data inputs used by the checker. It is the exact JSON input used by
the imported Lean fixture and by the coverage source link.

The arithmetic fixture uses the full
`ec_classdata.anlist` and `ec_classdata.aplist` for 112.a, `ec_curvedata.torsion_primes`,
`ec_curvedata.potential_good_reduction` and `ec_curvedata.semistable` for 112.a2, and
the selected fields from both `ec_localdata` rows for 112.a2. The `anlist` decoder requires
a leading zero and checks coefficients 1 through 20 via the arithmetic L-function.
The `aplist` covers the first 25 primes, ending at 97, including the bad primes 2 and 7.
Both coefficient proofs concern the represented integral equation of 112.a2.
Transport to another member of 112.a requires independent isogeny or curve
identification evidence. Lean checks the failure of discriminant squarefreeness
from the equation. The joined capture does not include that field.

The 112.a2 local rows check additive reduction at 2, nonsplit multiplicative reduction at 7,
the discriminant and j-denominator valuations, and both arithmetic local signs.
At 7 the fixture also checks the canonical `I₁` symbol and the intrinsic Tamagawa factor 1.
The exact additive symbol and Tamagawa factor at 2 are outside this fixture's proofs.
The modular conductor comparison gives exponents 4 at 2 and 1 at 7 under the existing
modularity assumption.
The 179.a1 and 243.a1 fixtures also supply semistability, squarefreeness, and the local
discriminant valuation, j-denominator valuation, and reduction code from the snapshot.
The consumer checks the split multiplicative row at 179 and the additive row at 3.
The 179.a1 row also supplies the local Tamagawa factor 1 from the snapshot.
The compiled consumer checks the intrinsic factor in the completed field.
The 179.a1 row also supplies PARI Kodaira code 5 from the snapshot.
The consumer checks its canonical `I₁` symbol.

The 17.a2 Tamagawa fixture is a documented projection of row 19 of the pinned
John Cremona `ecdata` snapshot in `data/lmfdb/raw/curvedata-first-1200.txt`.
Its local arrays report prime 17, discriminant valuation 2, PARI Kodaira code 6
(I₂), and Tamagawa factor 2. The source snapshot revision, parser schema, and
Artistic License 2.0 attribution are recorded in `data/lmfdb/README.md` and
`data/lmfdb/raw/ECDATA-LICENSE`. This fixture requests the exact equation and
local arithmetic data only; it does not use the reference analytic rank.
`17.a2-tamagawa-joined.json` retains the producer-facing two-table projection
of the same row for the conditional kernel-replay test.

The 49.a4 Tamagawa fixture projects row 119 of that pinned `ecdata` snapshot
(Cremona label 49a1). Its p=7 row has type III (PARI code 3), discriminant
valuation 3, and Tamagawa factor 2. The 98.a5 p=7 row has a different additive
type (PARI code -5) and remains outside the checked Tamagawa scope. Both use
the source revision, schema, and Artistic License 2.0 attribution documented
in `data/lmfdb/README.md` and `data/lmfdb/raw/ECDATA-LICENSE`. The producer
joined projection retains the curve identity and its single local row; the
gated replay checks the accepted factor and rejects a corrupted value.
The checked JSON stores the producer's exact unit-scale change
`(r, s, t) = (2, 0, 6)` in its `tamagawa_type_iii` field.

The 50.a3 and 50.a1 Tamagawa fixtures project rows 123 and 124 of the same
pinned `ecdata` snapshot (Cremona labels 50a1 and 50a2). At p=5 both rows
have PARI type IV code 4 and discriminant valuation 4. Their respective
Tamagawa factors are 3 and 1. The checked fixtures supply the same exact
unit-scale change `(r,s,t) = (2,0,1)`. The split case gives the residue root 0,
and the nonsplit case gives Euler value 4 modulo 5. The joined projections
retain the native claims without the extra evidence, which the producer
proposes independently.

The 11.a2 and 26.b1 Tamagawa fixtures project rows 1 and 45 of the pinned
`ecdata` snapshot. Row 1 is split `I₅` at 11 with factor 5. Row 45 has split
`I₁` at 2 and nonsplit `I₇` at 13, each with factor 1. The producer proposes
either a checked node-polynomial root or the exact nonsplit Euler-power value.
The checked projections store that evidence; the producer-facing joined
projections retain the source rows without it so CI exercises proposal replay.
The verifier checks supplied evidence only. Higher multiplicative indices at
`p = 2` remain unsupported; the existing evidence-free I₁/I₂ routes are unchanged.

The Lean consumer checks the finite theorems and checks the modularity dependency
on conductor and root-number theorems. The matrix inputs contain no rank data. Its consumer also reuses the separate, already
checked analytic-rank-one witness for 112.a2 on the same integral equation.

The 112.a2 fixture also includes the point triples from the
[LMFDB Mordell–Weil generators table](https://www.lmfdb.org/EllipticCurve/Q/112/a/2#Mordell-Weil_generators).
The fixture also requests exact additive order 2 for the supplied torsion point.
The counts at the supplied good primes 3 and 5 verify a divisor of 2, which
proves the stored order and cyclic structure.
The consumer checks membership in the rational curve for points from both lists.
It checks the full rational torsion subgroup's prime support `[2]` and the cyclic
presentation sending the standard generator to the literal affine point `(-2, 0)`.

The 112.a2 fixture copies the published abc-quality decimal from the
[LMFDB curve page](https://www.lmfdb.org/EllipticCurve/Q/112/a/2#invariants).
Its separate error witness supplies a factorization of the reduced abc product
and asks Lean to prove an absolute error bound of `10⁻¹⁵`.
