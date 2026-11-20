# 1,000-curve validation benchmark

Run on 2026-11-20, on the macOS arm64 host recorded in the reports. Selection
was all 1,000 rows of `data/lmfdb-1000-additional.json`, in source order, spanning
182 conductors from 42 through 285; see the [snapshot provenance](../data/lmfdb/README.md).
No rank filter was used. Equations and
conductors alone were passed to the Lean witness producer; reference ranks were
compared only after mathematical validation.

Dependencies were prebuilt; setup builds are excluded and OS caches were not
flushed. Every timed candidate was checked from source, rather than reused as
an already compiled curve proof.

## Results

**952 distinct curves obtained kernel-checked, importable analytic-rank theorems:**
726 of rank zero and 226 of rank one. All 952 agree with the stored LMFDB analytic
ranks. These analytic conclusions retain the existing explicit modularity axiom;
numerical and finite arithmetic checks retain their standard-only axiom boundary.

| Phase | Active elapsed seconds | Child CPU seconds |
| --- | ---: | ---: |
| Generate witnesses for all 1,000 inputs | 20.129 | 13.971 |
| Initial validation, batches of at most 20 curves | 896.033 | 684.271 |
| Retry 245.a1 after fixing serialization | 18.692 | 10.206 |
| Combined validation | **914.725** | **694.477** |
| Final import/use of all 952 compiled rank theorems | 5.422 | 6.262 |

Combined validation averaged **0.961 seconds per successful certificate**,
including batch imports and `.olean` output. Generation and compiled-proof reuse
are separate phases. This is a single dataset run, not 1,000 independent Lean
startups. The final reuse check was a new ordinary Lean module importing all
successful compiled modules and applying every exported rank theorem.

This average does not guarantee a two-second bound for every curve: the larger
245.a1 witness alone took 18.692 seconds in a fresh process. The selected curves
have small conductors, and many are isogenous. The result is not an extrapolation
to all LMFDB curves, higher ranks or arbitrary numerical parameters.

## Inconclusive cases and the bug found

48 inputs stopped at the sufficient minimality criteria. A separate Lean audit
checked all 48 exact `minimalityWitness? = none` equations using `decide +kernel`.
Every discriminant-factorization support check matched. The insufficient local
criteria were at prime 2 for 44 inputs and prime 3 for four inputs. These are
inconclusive checks, not proofs that the equations are nonminimal. No analytic
rank theorem was claimed for them. Labels and failed primes are in the follow-up
report.

The initial run checked 951 curves, stopped on those 48, and rejected one witness
for 245.a1. Its 64-coefficient witness was truncated by Lean's display-oriented
pretty printer into syntax containing `⋯`. `certify_ec` now enables deep terms and
proofs, uses its own serialization budget, and explicitly rejects any residual
display omission. It still verifies the supplied data with the kernel. Regression
coverage includes that curve under restrictive display options and a round-trip
at the JSON profile's maximum 128-coefficient count.

The original 245.a1 JSON witness then validated unchanged. Its compiled theorem
was imported together with the other 951, giving the final total of 952.
The initial run's production sources were at `aebaea0`; its benchmark harness is
preserved at `306289f`. The reports retain the original rejection and record the
retry separately, with source and witness fingerprints.

## Timing clocks

On this host Python's `perf_counter` uses `mach_absolute_time` and excludes system
suspension. Lean's `IO.monoNanosNow` uses C++ `steady_clock`, which included
suspension in the observed run. The raw report contains affected command samples
longer than their enclosing active-time batches. Those are not computation
outliers and must not be used as an active-time latency distribution. Per-conductor
command-time sums have the same limitation. The table
uses the Python active-time measurements and separate child CPU measurements.
The machine was suspended during the experiment, so human waiting time was longer.

The runner now also records an outer clock matching Lean's clock on macOS. The
original raw timings and the identified clock disagreements remain in the report.
Lean's implementation is in the pinned
[runtime source](https://raw.githubusercontent.com/leanprover/lean4/v4.36.0-rc2/src/runtime/io.cpp).

## Artifacts and reproduction

- [Initial measurements and per-curve outcomes](../output/certify-ec-performance/dataset-1000.json)
- [245.a1 retry, final reuse check and minimality audit](../output/certify-ec-performance/dataset-1000-follow-up.json)
- [Benchmark workflow and bounded numerical schedule](../benchmarks/README.md)

Generated witnesses, Lean files and compiled modules are local experiment output
under `.lake/ec-dataset-f93eaf54653e8a2f/`. Successful batch modules are
`Batch0000` through `Batch0047`; the retry is `Retry245`, exporting
`Curve245.analytic_rank`. `ConsumerFinal.lean` imports and uses all 952 theorems.
The initial batch `.olean` files alone occupy about 17.9 MB; this does not include
shared dependencies or all ancillary compiler output. No bulk proof corpus or
new distributed cache has been checked into the repository.

For a fresh run:

```sh
python3 scripts/benchmark_ec_dataset.py --count 1000 --batch-size 20 \
  --output output/certify-ec-performance/dataset-new-run.json
```
