# Certificate checking performance

The [1,000-curve benchmark](CERTIFY_EC_DATASET_BENCHMARK.md) subsequently produced
952 certificates in 915 seconds of active validation time, including a retry
after a serialization fix. The remaining 48 inputs hit insufficient minimality
criteria. That report separates batch throughput, setup, import reuse and clocks.

## Current implementation (2026-11-20)

Validation remains `decide +kernel`, with the same axiom audits and supplied
witnesses. The metaprogram itself is unchanged. The optimization is mathematical:

- At odd primes, count each x-fiber by completing the square and applying
  Mathlib's `quadraticChar_card_sqrts` and Euler criterion. Explicit Mathlib
  binary exponentiation replaces enumeration of all y values. The resulting
  evaluator is proved equal to the existing finite-ring point count, including
  singular models. Characteristic two and composite moduli keep the general path.
- Interval multiplication selects extremal products from endpoint signs when
  possible, avoiding unnecessary rational products and comparisons in Horner
  evaluation. Its real enclosure theorem is proved for arbitrary containing
  intervals; the mixed-sign case retains the four-corner formula.

The current fresh-process measurements are three sequential repetitions on
macOS arm64, with prebuilt dependencies and no OS cache flushing:

| Operation | Median wall seconds | Median child CPU seconds |
| --- | ---: | ---: |
| Lean without checker imports | 0.327 | 0.267 |
| Import checker only | 3.965 | 3.061 |
| Import and reuse compiled theorem | 3.077 | 2.801 |
| Validate 11a1, rank zero | 4.355 | 3.297 |
| Validate 37a1, rank one | 4.105 | 3.764 |
| Validate 112a2, wild additive rank one | 5.446 | 4.718 |
| Validate all three distinct curves in one module | 8.175 | 6.308 |

The three-curve batch therefore averages **2.725 seconds per curve**, including
one import. These are fresh source checks producing `.olean` files, not imports
of already checked curve proofs. Single-curve fresh processes still take about
4–5.5 seconds, largely because of loading the checker. Import times vary with
OS cache and scheduling; their reduction is not an algorithmic speedup.

Separate, single-run profiler samples measure the `certify_ec` command after
imports: **0.216s** (11a1), **1.164s** (37a1), and **1.831s** (112a2). These include
JSON elaboration, finite checks, theorem construction and axiom audits. They are
profile samples, not the medians in the table. The conductor-112 payload's
kernel check fell from **6.004s to 1.509s** in the corresponding profile samples.

The matched pre-point-count-optimization batch took **17.237s wall / 10.219s
CPU**, versus **8.175s / 6.308s** now. That baseline already includes sign-based
interval multiplication; it isolates the subsequent odd-prime counting change,
subject to ordinary timing variability. The before/after reports use the same
three witness hashes. This is a small regression benchmark, not a claim about
all LMFDB curves or large coefficient prefixes.

Raw samples, toolchain/source/witness fingerprints and separate profiler logs:

- [Before odd-prime counting](../output/certify-ec-performance/before-odd-point-count.json)
- [Optimized implementation](../output/certify-ec-performance/optimized.json)
- [112a2 before profile](../output/certify-ec-performance/before-odd-point-count-logs/112a2-profile.log)
- [112a2 optimized profile](../output/certify-ec-performance/optimized-logs/112a2-profile.log)

Reproduce with:

```sh
python3 scripts/benchmark_certify_ec.py --launcher direct --repetitions 3 \
  --profile --output output/certify-ec-performance/new-run.json
```

`--launcher direct` asks Lake for `LEAN_PATH` once, then launches the pinned Lean
binary directly for each fresh process. The default `--launcher lake` includes
Lake invocation in every sample. Both build dependencies before timing. The
benchmark records wall and child CPU time, includes a batch of three distinct
curves, and saves completed measurements incrementally. `--cases` selects a
subset; profiling runs separately from timed repetitions.

For normal use, put several `certify_ec` commands in one module, as in
`examples/certify_ec/CertifiedCurves/Json.lean`, and compile it once. Each command
still performs all its checks and exports its own named theorems. This amortizes
imports without introducing a service or relying on unchecked cached claims.

The remaining numerical hot path is rational quadrature. Further work can
consider a proved fixed-point Horner evaluator and sharing checked numerical
facts between appropriate curves. Neither optimization is implemented here.

## Historical measurements

These measurements describe the implementation at `8f5205e`, **before** the
requested migration from `Artifacts.CurveEquation` to mathlib's
`WeierstrassCurve ℤ`. They do not establish post-migration performance.

Run the reproducible process benchmark with:

```sh
uv run python scripts/benchmark_certify_ec.py --repetitions 3 \
  --output output/certify-ec-performance/new-run.json
```

The script builds dependencies first, then distinguishes fresh source checking,
pure imported-theorem reuse, and warm Lake reuse. It records wall time and child
CPU time, exact command/witness hashes, toolchain and mathlib revision. Every
certificate is checked by Lean. Python only orchestrates and times processes.
A fresh process is not a cold OS file cache; no file caches were flushed here.

## Pre-migration baseline

Three sequential repetitions on this machine produced these wall-time medians:

| Operation | Seconds |
| --- | ---: |
| Import checker, no certificate | 2.508 |
| Import compiled proof and prove a new theorem from it | 2.501 |
| Check supplied rank-zero witness, conductor 11 | 2.973 |
| Check supplied rank-one witness, conductor 37 | 3.525 |
| Check supplied wild-additive rank-one witness, conductor 112 | 5.863 |
| Warm Lake build of existing certificate library | 2.640 |

Raw samples and CPU measurements are in
[`baseline.json`](../output/certify-ec-performance/baseline.json). Import/loading
accounts for a substantial part of a fresh process. In an earlier first-load
sample the empty import took 11.60 seconds, falling to 2.65 seconds on repetition;
that variability must not be advertised as a verification optimization.

The kernel profiler on conductor 112 attributed about 2.259 seconds to
`payload_correct` reduction within a 2.386-second certificate command. Other
individual elaboration/audit phases were below 20 milliseconds. Lean's imported
axiom cache already prevents every `collectAxioms` call from traversing the
entire imported analytic library.

## Experiments performed and reverted

1. One decidable conjunction for all finite checks, followed by named component
   projections through proved soundness lemmas. It compiled and preserved the
   mathematical premises, but fresh-process medians were worse: conductor 37
   3.736s versus initial 3.455s, conductor 112 6.828s versus 5.204s. OS cache
   variability prevents precise causal attribution; there was no demonstrated
   improvement warranting the added proof abstraction.
2. Check equality with one fixed evaluator output, then obtain payload validity
   from the existing `evaluate*_correct` theorems. Conductor 37 was slower
   (3.981s); conductor 112 improved only about 4% wall time and 6% in the profiled
   payload reduction. This was not a meaningful overall improvement and was
   also reverted.

[`experiments.json`](../output/certify-ec-performance/experiments.json) retains
these samples. The production command was restored exactly; no witness
condition, axiom audit, rejection behavior or kernel trust requirement changed.
Neither `native_decide` nor precomputed claims of success were used.

The first exploratory consumer timing included `#eval` and `#print axioms`, so
it was not a pure proof-import measurement. The final `cached_proof` measurement
uses an ordinary theorem applying an imported proof, without evaluation or
numerical replay. Comparing `#eval` with `#reduce` for displaying the already
certified Nat, and explicitly testing import while JSON files are unavailable,
was prepared but not run before the representation migration took build
ownership. No result is claimed for either pending test.
