# Importing certificates and assembling a mathematical database

## Browse the hosted certificates

The [curve certificate companion](https://khwilson.github.io/verified-lcalc/)
indexes successful manual benchmark runs published from `main`. Look up an
LMFDB label to see the checked facts, their Lean names and project-specific
assumptions. The link to LMFDB opens the corresponding curve record.

The first three facts are nonsingularity of the supplied equation, global
minimality of its integral model, and exact analytic rank. The rank theorem
uses `VerifiedLcalc.Assumptions.ellipticModularity`. Each published value is
checked by a fresh Lean process importing the compiled module. The same import
checks the equation against the five input coefficients and the conductor in
the numerical result against the selected input. Inconclusive rows carry no
published facts. A label outside the published runs has no entry.

Each checked entry links directly to its batch's `.olean` and to a ZIP with
the module's companion files. Several curves can share one download. To use
the bundle, check out the project's linked commit, install its pinned Lean
toolchain and build `VerifiedLcalc.Tactic.CertifyEC`. Extract the ZIP into
an empty directory and verify its checksums. Create a Lean file that imports
the displayed module and uses `#check` on the displayed theorem name.
From the repository checkout, run the file with the extracted module directory
on Lean's search path:

```sh
deps="$(lake -f lakefile.certificates.lean env printenv LEAN_PATH)"
LEAN_PATH="/absolute/path/to/extracted-module:$deps" lean UseCertificate.lean
```

The underlying [certificate releases](https://github.com/khwilson/verified-lcalc/releases)
include the machine-readable catalog and asset checksums for each run. The
raw benchmark statistics are a separate artifact on the Actions run page.

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
