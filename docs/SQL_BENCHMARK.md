# SQL snapshots and conductor benchmarks

LMFDB documents its read-only PostgreSQL mirror at
<https://www.lmfdb.org/api/options>: host `devmirror.lmfdb.xyz`, port `5432`,
database/user/password `lmfdb`. The user downloaded the 10,000-curve snapshot on
2026-11-18. Its hashes, raw-to-input records, exclusion list and label ordering
have been checked locally. The snapshot spans 1,171 conductors, 285 through
1968; the final conductor is partially selected. See the captured
[data provenance](../data/lmfdb/sql-10000/README.md).

From this project directory, download exactly 10,000 additional curves:

```sh
uv run scripts/download_lmfdb_sql.py
```

The downloader uses one read-only, repeatable-read SQL transaction. It selects
by conductor and label, excluding all 1,100 existing labels, without filtering
on analytic rank. It reads the actual `analytic_rank` column, never substitutes
Mordell-Weil rank, and preserves null reference values. Integral coefficients
are transferred through PostgreSQL's JSON conversion to avoid floating-point
rounding of numeric arrays.

The directory `data/lmfdb/sql-10000/` receives `raw.json`, `inputs.json`,
`references.json`, and `provenance.json`. The provenance records the exact query,
excluded labels, snapshot time, hashes, attribution and license source. The
producer receives only `inputs.json`; expected ranks reside in a separate file.
Existing snapshots are not overwritten. An exact count can split the final
conductor: provenance explicitly records whether that boundary is complete.
This is coverage of selected curves, not a claim to cover every curve at every
selected conductor. `LMFDB_HOST`, `LMFDB_PORT`, `LMFDB_DBNAME`, `LMFDB_USER`, and
`LMFDB_PASSWORD` can configure another reachable copy.

Run the benchmark in increasing conductor order:

```sh
python3 scripts/benchmark_conductors.py \
  --references data/lmfdb/sql-10000/references.json \
  --provenance data/lmfdb/sql-10000/provenance.json
```

Use `--resume` to revalidate completed conductors and preserve their original
timings after interruption. Completed results are checkpointed conductor by
conductor under `output/conductors/`. Resume checks input, engine and audit
identities, saved proof source hashes, the Lean dependency graph, and component
axiom lists. An existing report requires `--resume` or a different output path.

## Proof and audit stages

All numerical and arithmetic implementation remains in Lean. The Python scripts
perform download, orchestration, timing and external-reference comparison. The
Lean candidate producer never reads reference ranks. Its proposed numbers are
accepted only after both the proof module and an independently generated input
binding module compile. The binding checks each label, equation and conductor
against the requested JSON using a separate parser. It also typechecks every
reported rank and lower bound against its theorem, checks every component has
the required mathematical type, and binds precision, Fourier length and grid
settings to the actual payload. Component inventories have mandatory entries
for exact-rank claims; the producer cannot choose to omit those audits.

Each curve has named, individually audited theorems for the available components:

- nonsingularity;
- finite minimality witness and its implication of global minimality;
- local Tate/root-table transcript validity;
- mathematical conductor and root-number formulas;
- agreement of executable coefficients with the actual curve Euler coefficients;
- finite numerical payload correctness, when an interval separates zero;
- exact analytic rank and negative-sign lower bounds, where established.

The global `Audit*.lean` checks run before the campaign. `AuditIntervalComponents`
explicitly guards rounding, interval addition, Horner evaluation, interval sums,
polynomial/Fourier tails, exponential bounds and the evaluator's finite contract.
Every conductor also prints axiom dependencies for every named concrete component.
The runner checks that all required audits are present. Arithmetic and numerical
components may use only the standard Lean/mathlib axioms; analytic curve results
may additionally use the existing `ellipticModularity` axiom. No assumption has
been added or expanded for the larger fixture.

Proof modules use a namespace derived from input and engine hashes and are
separate from the installed 1,100-curve registry. The benchmark does not silently
install new results into that backend. Failed proofs, missing audits, unexpected
axioms, subject mismatches and external-reference mismatches stop the run.
Unsupported arithmetic and intervals containing zero remain explicitly
inconclusive. No expected rank is used to make them resolve.

## Timing interpretation and limits

Each conductor records candidate-production time, first kernel-build time, warm
cache-validation time, source hashes, component count and per-curve results.
Prerequisite build and global-audit time are separate. `prior_artifact_exists`
identifies already cached proof modules; these are not cold timings. Resume
retains original build times and appends validation times. Warm validation
reuses checked `.olean` files after dependency checking; it is not fresh kernel
replay of unchanged proofs. No timing for 10,000 new curves is claimed until
that snapshot has actually been downloaded and processed.

The default process wall limit is 3,600 seconds (`--timeout` adjusts it). A timed
out process group is stopped, a failure is checkpointed, and no result for that
conductor is accepted. The numerical search limits are recorded in each report:
central prefixes through 128 terms and precision through 106 bits; derivative
prefixes through 128 terms at the global 53-bit precision, with cutoffs through
64 and grids through 16 cells per unit. Exhaustion is inconclusive. Conductors
are built sequentially with `LEAN_NUM_THREADS=2` by default to limit memory use.

The initial local smoke test used 23 existing curves at conductors 11, 27, 37
and 112. It checked 180 named concrete components, produced 17 conditional exact
rank certificates with no reference mismatches, and left six minimality cases
inconclusive. First kernel builds took approximately 10–17 seconds per
conductor, with warm validation around six seconds. These are smoke measurements
on existing fixtures, not measurements for the proposed SQL expansion.

## Campaign progress

The full SQL campaign writes `report.json`, `summary.json`, `TIMINGS.md`, and
`timings.csv` under `output/conductors/S71fbc342c387d481_Ef0de62a8fa947616_Rf5d46605de175918/`.
These update after each conductor. `complete` means every selected curve has
been processed; it does not mean every analytic rank was resolved. The report
preserves first-build timings and records subsequent validation separately.

Validation version 2 binds output metadata to the actual mathematical theorems.
The early version-1 conductors are revalidated with the stronger bindings before
counting them in the resumed run. The original numerical proof modules remain
cached. An intentionally changed reported rank was rejected by Lean's type
checker. `session_elapsed_seconds` measures the latest invocation; per-conductor
build timings survive resume. Summed stage times and session wall time have
separate labels.
