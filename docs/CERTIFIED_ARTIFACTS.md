# Importing certificates and assembling a mathematical database

## Browse the hosted certificates

The [curve certificate companion](https://khwilson.github.io/verified-lcalc/)
indexes successful manual benchmark runs published from `main`. Look up an
LMFDB label to see the checked facts, their Lean names and project-specific
assumptions. The link to LMFDB opens the corresponding curve record.

Checked rows identify the nonsingular, globally minimal integral equation and
give its exact analytic rank under `VerifiedLcalc.Assumptions.ellipticModularity`.
Schema 2 catalogs also expose the existing arithmetic checks from the same rank
witness.

| Catalog field | Lean theorem | Checked statement |
| --- | --- | --- |
| `arithmetic_conductor` | `conductor_valid` | `wildLevelFast` on the equation and verified local transcripts equals the displayed level. |
| `arithmetic_root_number` | `root_number_valid` | `wildSignFast` on the same data equals the displayed sign. |
| `l_function_coefficients` | `l_function_coefficients` | An exact prefix of the arithmetic L-function coefficients starting at index 1. |
| `discriminant_prime_factorization` | `minimality_valid` | The displayed primes, repeated with multiplicity, multiply to the absolute discriminant and pass the model minimality test at each prime. The catalog omits this entry if the list is empty. |

These theorem statements use only the finite checks, with no project
axioms. Geometric conductor and epsilon-factor compatibility used for the
analytic rank remain part of the modularity assumption. Each published value
is bound to the theorem's type by a fresh Lean process importing the compiled
module. The same import checks the five input coefficients and the conductor
used by the numerical result against the selected input. Replay repeats these
value checks when compiling the archived witnesses. Existing schema 1 catalogs
retain their original three fields. Inconclusive rows carry no facts.

When a release includes compiled modules, each checked entry links to its
batch's `.olean` and to a ZIP with the module's companion files. Several
curves can share one download. To use the bundle, check out the project's
linked commit, install its pinned Lean toolchain and build
`VerifiedLcalc.Tactic.CertifyEC`. Extract the ZIP into an empty directory and
verify the bundle hash against the catalog. Create a Lean file that imports
the displayed module and uses `#check` on the displayed theorem name. From
the repository checkout, run the file with the extracted module directory on
Lean's search path as follows.

```sh
deps="$(lake -f lakefile.certificates.lean env printenv LEAN_PATH)"
LEAN_PATH="/absolute/path/to/extracted-module:$deps" lean UseCertificate.lean
```

## Inspect field dependencies

Open the [dependency roadmap](https://khwilson.github.io/verified-lcalc/roadmap.html)
to trace a table-qualified LMFDB field from its mathematical prerequisites
through its Lean witness and producer. Select a node to follow its inputs or
outputs. Search by table, field, or evidence, and use the filters to find
missing components. Alternative routes apply under their own hypotheses.
The fixture samples correspond to their displayed curves and proof scopes.

When editing the catalogue or producer, regenerate the Lean contract and
single-curve replay snapshots after building the verifier.

```sh
python3 scripts/check_lmfdb_dependency_contracts.py --write
python3 scripts/check_lmfdb_producer_example.py --write
python3 scripts/build_lmfdb_dependency_roadmap.py --write
```

The existing
**Refresh certificate companion** Pages workflow assembles the roadmap,
fixture audit, and published curve catalogues together from `main`.

## Verify and replay a signed release

New releases contain `catalog.json` and `witnesses.jsonl.gz`, both signed by
the certificate batch workflow on GitHub-hosted runners. The catalog records
the selected input and checked facts, the pinned source and dependency
revisions, and the archive digest. The compressed JSON Lines archive supplies
the exact `certify_ec` witnesses for checked curves. The raw benchmark report
is a separate Actions artifact.

For the fixed [2026-11-18 LMFDB snapshot](../data/lmfdb/sql-10000/README.md),
the ten aligned 1,000-curve slices have display labels
`lmfdb-2026-11-18-batch001` through `lmfdb-2026-11-18-batch010`.
The companion derives the label from the catalog's snapshot SHA-256, offset,
and count and displays the exact Lean version recorded in the catalog.
New releases of these slices use the label and Lean version in their titles.
Use the immutable `ec-certificates-RUN_ID-ATTEMPT` release tag when downloading
or verifying artifacts.

With an authenticated GitHub CLI (`gh auth login`), run the following in a
Bash shell. Set `tag` to a tag from the certificate releases and use an empty
download directory. This verifies both files against the expected repository,
workflow, main branch, and source commit recorded by the Actions run.
[Certificate releases](https://github.com/khwilson/verified-lcalc/releases) ·
[GitHub attestation verification](https://cli.github.com/manual/gh_attestation_verify)

```bash
set -euo pipefail
repo=khwilson/verified-lcalc
tag=ec-certificates-RUN_ID-ATTEMPT
[[ "$tag" =~ ^ec-certificates-([0-9]+)-([0-9]+)$ ]]
run_id=${BASH_REMATCH[1]}
attempt=${BASH_REMATCH[2]}
revision=$(gh api "repos/$repo/actions/runs/$run_id/attempts/$attempt" --jq '.head_sha')
[[ "$revision" =~ ^[0-9a-f]{40}$ ]]
downloads=$(mktemp -d)
gh release download "$tag" --repo "$repo" --dir "$downloads" \
  --pattern catalog.json --pattern witnesses.jsonl.gz --pattern provenance.sigstore.json
for file in catalog.json witnesses.jsonl.gz; do
  gh attestation verify "$downloads/$file" --repo "$repo" \
    --signer-workflow "$repo/.github/workflows/certificate-batch.yml" \
    --source-ref refs/heads/main --source-digest "$revision" \
    --deny-self-hosted-runners \
    --bundle "$downloads/provenance.sigstore.json"
done
```

Keep `provenance.sigstore.json` along with both files when mirroring a release.
The bundle preserves the signed evidence and lets `gh` skip the repository's
attestation lookup. Omit `--bundle` to use the registered attestation from
GitHub. For offline verification, supply a previously obtained trusted root
with `--custom-trusted-root` and obtain the expected commit through a trusted
channel before going offline. [GitHub offline verification instructions](https://docs.github.com/en/actions/how-tos/secure-your-work/use-artifact-attestations/use-artifact-attestations#verifying-attestations-offline)

Use a clean checkout of the verified commit and install its pinned Lean
toolchain. For a fresh checkout, follow the
[dependency cache instructions](BUILD.md) before building the verifier.
The replay reads the catalog and witnesses, builds the pinned verification
library as needed, and invokes Lean on the supplied witnesses. Pass
`--curve LABEL` to replay one checked curve. Omit it to replay the batch.

```bash
git checkout --detach "$revision"
elan toolchain install "$(cat lean-toolchain)"
python3 scripts/replay_ec_batch.py "$downloads/catalog.json" "$downloads/witnesses.jsonl.gz"
```

Attestation verification establishes the files' provenance and integrity.
Lean replay checks the mathematical claims under their stated assumptions.
Older releases published before signing began remain available for compiled
proof import and checksum verification. Their catalogs predate the signed
replay records and may lack a witness archive.

The manual workflow publishes the signed catalog and witnesses by default.
Enable `publish_modules` to include compiled modules and ZIP bundles for
immediate import. The replay command works for either kind of release.

## Import the existing local certificates

From the repository root, create `UseCertificate.lean` containing:

```lean
import Batch0000

#check Curve0000.curve
#check Curve0000.analytic_rank  -- 42.a5
```

Run it with the local artifacts and pinned dependencies on the search path:

```sh
lcalc_library_path="$(lake -f lakefile.certificates.lean env printenv LEAN_PATH)"
LEAN_PATH="$PWD/.lake/ec-dataset-f93eaf54653e8a2f:$lcalc_library_path" \
  lean UseCertificate.lean
```

This loads the compiled theorem; it does not rerun `certify_ec`. The initial
[1,000-curve report](../output/certify-ec-performance/dataset-1000.json) maps
labels to `module` and `index`: index 123 corresponds to
`Curve0123.analytic_rank`. Only rows marked `checked` have certificates in that
initial run. The [retry](../output/certify-ec-performance/dataset-1000-follow-up.json)
for 245.a1 is `import Retry245`, with `Curve245.analytic_rank`.

The SQL benchmark uses a distinct `SQL10000` prefix for both module and
declaration names, so its artifacts can coexist with the earlier dataset.
New reports explicitly record `declaration_prefix` for each validation attempt.
The report's `work_directory` locates that run's compiled modules.

## Database layout and compatibility

A scalable design has four parts:

1. An environment record pins Lean, Mathlib, TauCeti, the certification library,
   build settings and dependency fingerprints.
2. A fact catalog maps a mathematical subject/property to its Lean module and
   theorem name, statement, axiom dependencies and artifact bundle.
3. Immutable artifact storage holds independently checked batch modules and their
   sources/manifests. Preserve the complete set of artifacts required by Lake,
   including relevant module sidecars and dependencies.
4. Snapshot manifests list a compatible set of accepted batches. A snapshot can
   generate an umbrella module:

   ```lean
   module
   public import CertifiedEC.EnvironmentA.Shards.Batch0001
   public import CertifiedEC.EnvironmentA.Shards.Batch0002
   ```

The umbrella re-exports the constituent facts. It references the batch modules;
it does not copy their proof bodies into one physical binary. Adding a batch
updates the manifest and umbrella while preserving the existing compiled batches.
Lean's [module system](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
and [Lake build graph](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
provide the underlying composition and incremental-build mechanisms.

Use globally unique module and declaration names. For example, an artifact
namespace can include an environment identifier and immutable shard identifier;
a catalog can supply stable user-facing names for facts. Two independent batches
must import the same canonical core rather than redefine shared mathematical
objects. Different labels must not accidentally introduce duplicate constants.

The catalog can be SQL or another index. A query should return the required
module/theorem and generate a small import file or package manifest. Loading a
specific curve can then import its batch alone. Importing an umbrella for every
stored fact is optional and becomes costly as the database grows. Ordinary Lean
imports belong in the file header, so dependency resolution happens before the
consumer's declarations are elaborated.

## Compatibility and trust

A single catalog can hold compiled variants for several dependency environments.
An individual Lean client selects one compatible environment: putting two Mathlib
versions' certificates into separate namespaces does not make their underlying
Mathlib definitions compatible. Rebuild portable sources for another environment
and record that result as another artifact variant of the same logical fact.

Ingestion should rebuild submitted sources or validate their serialized kernel
environments before accepting an artifact. Lean documents `lean4checker` for
checking `.olean` environments in its
[compilation reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/).
Ordinary imports subsequently reuse the accepted compiled environment without
replaying the original numerical computation. Artifact hashes identify bytes;
the acceptance process supplies the evidence that they were checked.

Record axioms explicitly. Our analytic-rank facts retain the authorized
`ellipticModularity` assumption; finite numerical checks do not acquire it merely
because they share a package or database. The catalog's subject and predicate
schema should distinguish exact ranks, conditional ranks and precision-small
observations. SQL metadata itself never becomes a Lean proof.
