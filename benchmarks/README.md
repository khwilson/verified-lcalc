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
