# Dataset validation benchmark

Run from the repository root:

```sh
python3 scripts/benchmark_ec_dataset.py --count 1000 --batch-size 20 \
  --output output/certify-ec-performance/dataset-new-run.json
```

The default source is the existing 1,000-curve supplemental snapshot, in source
order and without a rank filter. The Python runner strips reference ranks before
passing equations and conductors to Lean. `ProduceECWitnesses.lean` explicitly
searches a bounded numerical schedule using the existing exact Lean evaluators,
minimality witness generator, and wild-reduction witness generator. This search
is benchmark plumbing; its output is untrusted data, not a mathematical theorem.
Every successful JSON serialization is round-tripped through the real decoder.

`ValidateEC.lean` supplies a timing wrapper around the real `certify_ec` command.
The wrapper records rejected commands and rolls their state back; it does not
introduce axioms, substitute expected ranks, or bypass kernel checking. Ordinary
named theorems are emitted for successful cases. Distinct batches use distinct
harness namespaces so their compiled modules can be imported together.

The runner launches the pinned Lean binary with a library path resolved once
through Lake. Each batch starts a new Lean process and writes a new `.olean`;
its wall and CPU measurements include import, checking, and serialization.
Individual command timings exclude process imports and output serialization.
On macOS they use a different clock from Python’s active-elapsed timer: Lean’s
clock includes system suspension. The runner now records a matching outer clock
as well. Use active batch time and CPU time for computation-throughput claims;
do not treat suspend-affected command outliers as slow mathematical checks.
A final separate Lean process imports all successful batch modules and applies
every exported analytic-rank theorem. Reference ranks enter only afterward for
a separate comparison. Analytic theorems retain the existing modularity axiom.

Generation time, individual validation times, batch wall/CPU times, quantiles,
conductor summaries, failed/inconclusive outcomes, fingerprints and import-reuse
results are saved in the report. Conductor summaries add individual command
times; startup for a batch spanning several conductors is not assigned to one
conductor. Generated JSON witnesses, Lean sources, logs
and compiled artifacts stay in the ignored `.lake/ec-dataset-<fingerprint>/`
directory. The report includes that path for inspection. These artifacts are
rebuildable local experiment output, not a distributed proof cache.

The default numerical search tries central prefixes of 4, 8, 16, 24, 32, 48, 64,
96, and 128 terms at 53 bits. Negative-sign cases try derivative settings
`(terms, steps_per_unit, cutoff)` of `(24,1,8)`, `(32,1,12)`, `(48,1,16)`,
`(64,2,16)`, `(96,4,24)`, and `(128,8,32)`. It stops at the first enclosure
excluding zero. An unsuccessful search is inconclusive. In particular, this
benchmark does not implement higher derivatives or improve the available
minimality criteria.

`--timeout` bounds each batch's wall time (default 900 seconds). A failed or timed
out batch is reported separately and none of its cases are counted as imported
certificates. `--resume` reuses completed measurements only when input, harness,
producer, runner, numerical implementation and configuration fingerprints agree.
Use a different output path for a fresh timing run; resumed work is not advertised
as a new measurement.

## SQL snapshots and independent runs

The rank-free SQL snapshot uses a separate reference file:

```sh
python3 scripts/benchmark_ec_dataset.py \
  --source data/lmfdb/sql-10000/inputs.json \
  --references data/lmfdb/sql-10000/references.json \
  --count 10000 --batch-size 20 --batch-work-limit 4000 \
  --consumer-modules 25 --module-prefix SQL10000 --workers 4 --timeout 3600 \
  --output output/certify-ec-performance/dataset-10000.json
```

Reference-file hashes enter the run identity; reference values are read only
after verification and compiled-proof import tests. The inputs and references
remain separate throughout the producer/validator pipeline.

The optional work cap partitions candidates by their supplied numerical settings:
`terms * max(1, steps_per_unit * (cutoff - 1))`. It never discards an expensive
candidate; a candidate above the cap runs alone. This bounds the amount of work
lost if a batch fails. It does not classify mathematical truth or use reference
ranks. Batch sizes are therefore at most 20, with smaller batches for larger
quadratures. The timeout is per batch and any timeout is reported explicitly.

Import checks use at most `--consumer-modules` batch modules per consumer, and
every successful theorem is applied in one of those consumers. This avoids
loading the complete 10,000-curve collection into a single process. Module and
declaration prefixes prevent independent datasets from colliding when imported
together; reports record the actual module and declaration names.

See [the artifact/import guide](../docs/CERTIFIED_ARTIFACTS.md) for current
imports and the proposed database/snapshot structure.

Witness encoding failures are recorded as `generation_error` for that input;
no candidate file or certificate is emitted for it. This lets a large campaign
record every input instead of aborting at the first unsupported encoding.

`--workers` defaults to one. Larger values run independent Lean processes with
distinct source and output files against prebuilt, read-only dependencies; the
initial Lake build remains sequential. The report records elapsed validation
phases separately from the sum of overlapping batch durations, and records CPU
usage from each worker's own child process. Use phase elapsed time for throughput.
Completed batches are checkpointed as they finish, including out-of-order results.

`--generation-report PATH` can adopt candidate witnesses from a completed
generation report. It checks the producer, mathematical sources, toolchain,
input identities and witness hashes, then checks each witness's curve and
conductor against the selected input. Proof-frontend changes are recorded
separately. Adopted witnesses remain untrusted: every certificate is rebuilt,
and no previous proof or validation status is reused. `--resume` instead resumes
an identical campaign, with all run fingerprints unchanged.

The validation template disables asynchronous elaboration inside each batch and
normalizes individual numerical obligations before `decide +kernel`. This allows
Lean to reuse identical auxiliary proofs within a module. Every curve still has
its own checked arithmetic obligations and exported theorem.
