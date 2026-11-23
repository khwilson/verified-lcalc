# Explicit assumptions

Keep one file per assumption family:

- `Modularity.lean` states `GeneralEllipticModularity` and declares the single
  authorized temporary axiom `ellipticModularity`. Its realization includes the
  documented arithmetic conductor and root-number compatibility.
- `Precision.lean` defines a curve-specific nonzero-gap hypothesis. It declares
  no axiom and supplies no instance of that hypothesis.

The ordinary precision policy lives in `VerifiedLcalc/Precision.lean`. A small
computed interval is not an exact zero. The optional hypothesis says that a
nonzero derivative must have a coordinate at least the specified gap, with a
strict margin between the numerical cutoff and that gap.

Canonical modular witnesses and analytic proofs live in
`EllipticCurve/Modularity/`. Certification and the conditional precision-upgrade
proofs live in `Verification/`. They must not be presented as assumptions.

Prefer conditional theorems taking the precision hypothesis as a parameter.
A downstream project choosing to postulate an instance must put that named
assumption in an explicitly imported file and document the exact curve,
precision, function normalization and derivative prefix. No blanket gap axiom
is authorized here. The exact rank-zero/rank-one `certify_ec` command rejects
additional axioms. Higher derivatives still require proved evaluators before
these hypotheses can upgrade real higher-rank numerical certificates.
