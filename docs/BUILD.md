# Build and cache

The workspace configuration uses `../mathlib4` to reuse its artifacts. Its
reviewed revision is `3440367ed1804626334f13a3a534a9cbb3385a59`. Since a local
path dependency does not lock its contents, verify that revision and local
changes before treating a run as reproducible:

```sh
git -C ../mathlib4 rev-parse HEAD
git -C ../mathlib4 diff --exit-code
```

For a standalone project, replace the `[[require]]` block in `lakefile.toml` with:

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "3440367ed1804626334f13a3a534a9cbb3385a59"
```

Then run `lake update`. Preserve the generated `lake-manifest.json`, which also
pins transitive dependencies. The `lean-toolchain` file pins the compiler.

Fetch targeted mathlib cache artifacts before building proofs:

```sh
MATHLIB_CACHE_DIR=/private/tmp/verified-lcalc-mathlib-cache lake exe cache get Mathlib.Analysis.Complex.Basic Mathlib.Analysis.Analytic.Order Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
lake build
```

Use a writable cache directory; the sandbox cannot write the user's default
`~/.cache/mathlib`. Cache misses for this mathlib development revision may still
need source compilation. Do not start concurrent builds of shared dependencies.
Integral curve inputs now use Mathlib's `WeierstrassCurve ℤ` directly, so the
computation core imports its canonical basic-curve definition. Keep analytic
proof imports out of standalone computation entry points where practical;
`certify_ec` itself is an elaboration-time verification command. The old
Std-only duplicate curve representation has been removed.

`make test-lean` builds the separate test library and audits theorem dependencies.
`lake build VerifiedLcalcTests.Fixtures.Cubic` checks and caches the saved certificate
module. `lake env lean tests/consumers/Cubic.lean` imports its compiled theorem.
`lake env lean tests/VerifiedLcalcTests/Fixtures/Cubic.lean` performs a fresh source replay.
Neither replay uses `native_decide`. See [the certificate contract](CERTIFICATES.md)
for request identity, proof obligations, and the distinction between importing
trusted compiled artifacts and checking their source again.


For the local certificate examples use `make certificates` (or
`lake -f lakefile.certificates.lean build CertifiedCurves`). The alternative Lake
configuration tracks JSON input files. For a standalone checkout, update its
`require mathlib from "../mathlib4"` to the same pinned dependency as the main
configuration, then preserve the resolved manifest. Retired generated batch
modules are not required or imported by this build.
