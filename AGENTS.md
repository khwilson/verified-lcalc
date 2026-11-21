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

- User-authorized exception (2026-11-17, clarified 2026-11-18): the sole temporary
  axiom `VerifiedLcalc.Assumptions.ellipticModularity` covers every nonsingular
  elliptic curve over Q, including additive reduction, with coefficient/Fricke
  matching and the documented semistable, tame and wild arithmetic conductor
  and root-number compatibility. Geometric Tate/Ogg and Halberstadt/local
  epsilon-factor compatibility remain part of that assumption. This does not
  authorize BSD, exact vanishing, numerical-correctness axioms, arbitrary input
  compatibility, or modularity over arbitrary number fields.
- Keep one assumption family per file: `Assumptions/Modularity.lean` and
  `Assumptions/Precision.lean`. The latter supplies explicit hypothesis records,
  not a blanket gap axiom. Mathematical proofs belong in `EllipticCurve/Modularity/`
  and `Certification/`, not in the assumption files.
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
- Fixed curve proofs and consumers live under `tests/VerifiedLcalcTests/` and
  `tests/consumers/`. Production modules must not import `VerifiedLcalcTests`.
- The registry/volunteer service, generated proof corpora, cached-key tables,
  legacy source installers and batch generators are retired. Baseline commit
  `fcdc4f2` preserves them. Do not recreate checked-in bulk proof blobs or
  advertise historical reports as an installed proof cache.
