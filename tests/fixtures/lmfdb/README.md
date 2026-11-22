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
finite local root numbers. The 2-adic transcript and first eight coefficients for 112.a2 come
from [the existing witness](../../../data/witnesses/112a2.json). The wild transcripts for 243.a1
and 288.a1 were computed with Lean's `wildData?` before being supplied to the verifier.
The 179.a1 and 243.a1 fixtures also supply semistability, squarefreeness, and the local
discriminant valuation, j-denominator valuation, and reduction code from the snapshot.
The consumer checks the split multiplicative row at 179 and the additive row at 3.
The Lean consumer checks the finite theorems and checks the modularity dependency
on conductor and root-number theorems. The matrix inputs contain no rank data. Its consumer also reuses the separate, already
checked analytic-rank-one witness for 112.a2 on the same integral equation.

The 112.a2 fixture also includes the point triples from the
[LMFDB Mordell–Weil generators table](https://www.lmfdb.org/EllipticCurve/Q/112/a/2#Mordell-Weil_generators).
The consumer checks membership in the rational curve for points from both lists.
