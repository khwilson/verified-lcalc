# verified-lcalc development

- Keep the mathematical implementation in Lean. Python may download data and
  orchestrate builds, benchmarks and tests; it does not certify mathematics.
- Computational routines need correctness theorems against mathematical
  specifications. Reuse Mathlib and TauCeti definitions and proved APIs.
- No sorry, unapproved custom axioms, unsafe arithmetic, native_decide
  certificates, or numerical tolerances presented as exact equalities.
- Use Mathlib's `WeierstrassCurve ℤ`, base change, invariants and decidable
  primality directly. Do not restore a duplicate curve-equation type.
- Fetch targeted Mathlib cache artifacts before compiling missing dependencies.
  Use a writable MATHLIB_CACHE_DIR and one Lake build owner at a time.

## Assumptions and proof boundaries

- User-authorized exception (2026-11-17, clarified 2026-11-18): the temporary
  axiom `VerifiedLcalc.Assumptions.ellipticModularity` covers every nonsingular
  elliptic curve over Q, including additive reduction, with coefficient/Fricke
  matching and the documented semistable, tame and wild arithmetic conductor
  and root-number compatibility. Geometric Tate/Ogg and Halberstadt/local
  epsilon-factor compatibility remain part of that assumption. By itself this
  does not authorize unrestricted BSD, exact vanishing, numerical-correctness
  axioms, arbitrary input compatibility, or modularity over arbitrary number
  fields. The separate narrow low-rank exception is recorded below.
- Keep one assumption family per file: `Assumptions/Modularity.lean`,
  `Assumptions/Precision.lean`, and the separately authorized
  `Assumptions/LowRankBSD.lean`. `Precision.lean` supplies explicit hypothesis
  records, not a blanket gap axiom. Mathematical proofs belong in
  `EllipticCurve/Modularity/` and `Certification/`, not in the assumption files.
- User-authorized exception (2026-11-22): the isolated opt-in
  `Assumptions/LowRankBSD.lean` may assume only the forward analytic-to-algebraic
  rank implications for exact analytic order zero and one over Q, using the
  same nonsingular equation and explicit arithmetic modular realization. Do not
  assume either converse or activate this family in the default library.
- Higher-rank upgrades require actual derivative enclosures, a specified nonzero
  gap strictly larger than the cutoff, and next nonvanishing for exact rank.
  Evaluators for derivatives two and higher are still missing.
- Arithmetic-only results and reference-data matches must not become analytic
  ranks. Never use expected LMFDB ranks to construct witnesses.
- Local reduction work lives under `EllipticCurve/Tate/`; distinguish proved
  transcript arithmetic from assumed geometric compatibility. Keep the GPL
  attribution/license with the wild root-number table implementation.

## Certificate workflow and validation

- `certify_ec` is the sole public command interface. Component-specific
  certifiers are backend helpers; all supported input methods share the same
  optional-field witness and verification dispatch.
- `certify_ec` accepts supplied Lean or exact JSON witnesses and verifies only.
  No search by default, native verification axiom, or leaked declarations after
  rejection. Audit finite and analytic theorem dependencies separately.
- `make certificates` builds the JSON-tracked example library.
  `make test-certificates` checks the command, JSON, conditional precision,
  finite cardinalities and compiled proof reuse.
- After mathematical changes, run `make test-lean`: it builds production and
  test libraries, replays cubic source/import tests, and runs arithmetic,
  numerical, general-modularity and axiom audits. Run `make check test` for the
  Python tooling. Do not run concurrent builds against shared dependencies.
- Every newly checked fact must be accessible as typed data and its exact
  proof through `Name.certificate`. Reuse indexed records and existing
  theorems. Add the raw field to the certificate coverage inventory and test
  an imported consumer. Use optional fields for absent evidence and a
  membership or bound type for partial evidence.
- Put canonical public certificate data and witness contract declarations in
  `VerifiedLcalc/Certificates/`. Reuse upstream Mathlib and TauCeti mathematical
  objects first; add only narrowly justified local specifications where the
  upstream API lacks the required encoding. Keep proof-only imports ordinary
  `import`s, and use `public import` only when the imported declarations occur
  in the public signature or are intentionally re-exported by an umbrella.
  Maintain the compiler-backed import audit and consumer at
  `tests/consumers/CertificateContracts.lean`.
- Keep realization-dependent facts parameterized over explicit realizations.
  The aggregate itself and new finite downstream projection theorems must
  pass the standard Lean axiom audit on a mixed certificate.
- Fixed curve proofs and consumers live under `tests/VerifiedLcalcTests/` and
  `tests/consumers/`. Production modules must not import `VerifiedLcalcTests`.
- The registry/volunteer service, generated proof corpora, cached-key tables,
  legacy source installers and batch generators are retired. Baseline commit
  `fcdc4f2` preserves them. Do not recreate checked-in bulk proof blobs or
  advertise historical reports as an installed proof cache.

## Pull requests and mathematical review

- Develop one independently reviewable change per PR against `main`. Merge a
  prerequisite before opening a dependent PR. Sol and Luna implement the
  changes. The coordinator reviews the diff, theorem statements and CI results.
- Before adding a mathematical declaration, search the pinned Mathlib and
  TauCeti sources, current upstream and open TauCeti PRs. Cite the declarations
  and source revisions used. Record missing general theorems and their intended
  hypotheses in the local TauCeti roadmap backlog for human upstream planning.
- Follow Mathlib style and document new public declarations. Explain the
  witness semantics, prerequisites and the strongest mathematical conclusion
  each new field exports. Retain attribution when porting an upstream result.
- Complete the TauCeti quality pass in the PR description and cite the roadmap
  target for new mathematics. Review the current head against the upstream
  rubrics for correctness, reuse, scope, hypotheses, API, naming, placement,
  proof quality, documentation and attribution. Record findings on the PR and
  recheck affected rubrics after revisions.
- Merge through a PR after the required GitHub checks pass on the candidate,
  including the ten-curve certificate suite. Use the ordinary protected-branch
  merge path. Check the axiom dependencies of new mathematical conclusions
  against this project's explicit assumptions above.

See the [TauCeti contributor rules](https://github.com/TauCetiProject/TauCeti/blob/main/AGENTS.md)
and [review rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/main/rubrics).
