# Lean and downloader regression tests

`VerifiedLcalcTests/Fixtures/` contains the small hand-written mathematical
fixtures formerly stored under `VerifiedLcalc/Certificates/`. The separate
`VerifiedLcalcTests` Lake library has `srcDir := "tests"`. Production modules
must not import it. `consumers/` checks reuse of compiled fixture theorems.

The generated batch corpora and old standalone source installers are retired.
The supported certificate interface is `certify_ec`, with its example library
under `examples/certify_ec/` and three small JSON witnesses under `data/witnesses/`.
Generic request/checker types remain under `VerifiedLcalc/Certificate*`; those
are library code, not a collection of curve certificates.

Run `make test-certificates` for command rejection, JSON, precision hypotheses,
finite cardinalities and compiled proof reuse. Run `make test-lean` for the full
project build, certificate tests and arithmetic/axiom audits. Python only
orchestrates those commands; all mathematics and mathematical checks are Lean.
