# Build and cache

Both Lake configurations import TauCeti from its published
[`v4.37.0-rc1` tag](https://github.com/TauCetiProject/TauCeti/tree/e0e414ce57522ba17560057ad0d7f2edab91bf0c).
The lockfile pins that revision, `e0e414ce57522ba17560057ad0d7f2edab91bf0c`,
and the matching [upstream Mathlib revision](https://github.com/leanprover-community/mathlib4/tree/31ce06eaadf4a200c0e1407c5f10953cf606b8f8).
Lake manages both source checkouts in `.lake/packages` using Lean `v4.37.0-rc1`.

Keep both Lake configurations, the manifest and the toolchain aligned when
updating a dependency. Historical reports retain their recorded dependency
revisions. A new benchmark records the actual Mathlib Git checkout selected by
its Lake configuration.

The two dependencies publish separate caches. In a Bash shell at the repository
root, load the TauCeti revision map, then fetch the Mathlib modules used by our
sources and by their TauCeti imports.

```bash
export LAKE_CONFIG="$PWD/scripts/tauceti-cache.toml"
export LAKE_CACHE_DIR="$PWD/.lake/cache"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export MATHLIB_CACHE_DIR="${TMPDIR:-/tmp}/verified-lcalc-mathlib-cache"
lake cache get --package=TauCeti --service=tauceti-public \
  --repo=TauCetiProject/TauCeti --rev=e0e414ce57522ba17560057ad0d7f2edab91bf0c --mappings-only
python3 scripts/mathlib_cache_roots.py > .lake/mathlib-cache-roots
xargs lake exe cache get < .lake/mathlib-cache-roots
lake build
```

Keep those environment variables set for subsequent Lake commands so direct
Lean replays can read the restored files. Use one Lake build owner per checkout.
The [Lean CI workflow](../.github/workflows/lean.yml) verifies the procedure on Linux.
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


For the local certificate examples use `make certificates` or
`lake -f lakefile.certificates.lean build CertifiedCurves`. The alternative
Lake configuration uses the same pinned Mathlib dependency and tracks JSON
input files for the examples and test fixtures.
