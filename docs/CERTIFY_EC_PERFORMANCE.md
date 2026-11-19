# Certificate checking measurements

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

## Next performance work

After the representation migration, rerun the benchmark and command regression
suite before making timing claims. The promising larger optimization is to
factor numerical quadrature/tail facts away from curve-specific arithmetic and
reuse kernel-checked numerical facts across isogenous curves sharing the same
coefficient prefix, conductor and precision settings. Alternatively, richer
intermediate arithmetic certificates could replace repeated large rational
reductions, but they require new soundness proofs. Neither is implemented here.
Batching several certificates in one Lean module can amortize process imports;
measure that separately rather than calling warm reuse a faster initial check.
