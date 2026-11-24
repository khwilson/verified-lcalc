# Certificate checking performance

The [1,000-curve benchmark](CERTIFY_EC_DATASET_BENCHMARK.md) subsequently produced
952 certificates in 915 seconds of active validation time, including a retry
after a serialization fix. The remaining 48 inputs hit insufficient minimality
criteria. That report separates batch throughput, setup, import reuse and clocks.

## Dyadic Horner evaluation (2026-11-24)

First-derivative quadrature keeps the outward-rounded exponential endpoints in
Lean's `Dyadic` type through Horner evaluation. Each step chooses the same
products and rounds in the same directions as the rational recurrence. Lean
proves equality of both endpoints for a nonnegative lower argument endpoint,
and proves that the exponential enclosure has this property. The finite
quadrature therefore returns exactly the previous rational endpoints. The
existing JSON witnesses, `decide +kernel` checks, and analytic proofs apply.

The comparison uses baseline `b1490ff`, Lean 4.37.0-rc1, and Mathlib
`31ce06ea` on macOS arm64. A warmup pair for each case was discarded.
The table reports medians of seven sequential baseline/candidate pairs with
the order alternating for each case. Both builds used prebuilt artifacts and
the same pinned dependency artifacts. Every sample starts a fresh Lean
process, with no operating-system cache flush. The initial import-only survey
overlapped another build on the host and is excluded here.

| Operation | Baseline wall s | Dyadic wall s | Baseline CPU s | Dyadic CPU s |
| --- | ---: | ---: | ---: | ---: |
| Lean without checker imports | 0.140 | 0.141 | 0.132 | 0.134 |
| Import checker only | 2.731 | 3.168 | 1.976 | 2.013 |
| Import and reuse compiled theorem | 2.903 | 3.030 | 2.005 | 2.019 |
| Validate 11a1 | 3.249 | 3.206 | 2.265 | 2.239 |
| Validate 37a1 | 3.559 | 3.869 | 2.490 | 2.447 |
| Validate 112a2 | 4.396 | 4.274 | 2.694 | 2.595 |
| Validate all three in one module | 4.990 | 4.913 | 3.253 | 3.148 |

The checker-only import wall times ranged from 2.19–3.38 s and 2.71–3.80 s.
The candidate was slower in all seven wall-time pairs. Its median CPU time rose
from 1.976 s to 2.013 s, with overlapping ranges (1.95–2.07 s and
1.97–2.05 s). The artifact paths differed and the comparison leaves the
cause of the import increase unresolved. Imported-theorem
reuse had nearly the same CPU cost as the checker-only import. The batch saved
CPU in six of seven pairs (median paired saving 0.102 s). Its wall-time ranges
overlapped (3.89–5.07 s and 4.69–4.97 s), with a median paired saving of 0.023 s.
The 112a2 source check saved CPU in all seven pairs, with a median paired saving
of 0.092 s. These measurements characterize the chosen workloads and host.

Seven separate profiler pairs measured the public command after imports. The
command profile includes JSON elaboration and axiom audits. The two kernel
columns measure named proof obligations inside that command.

| Case | Command before / after (s) | Coefficient kernel before / after (s) | Finite quadrature kernel before / after (s) |
| --- | ---: | ---: | ---: |
| 37a1 | 0.465 / 0.438 | 0.039 / 0.040 | 0.176 / 0.146 |
| 112a2 | 0.648 / 0.564 | 0.137 / 0.137 | 0.264 / 0.183 |

The finite quadrature check took less time in all seven pairs for both curves.
For 112a2, the kernel range fell from 0.257–0.277 s to 0.178–0.193 s.
The coefficient check serves as a control within the same command.

The exact JSON witness SHA-256 digests agree across the runs.

| Witness | SHA-256 |
| --- | --- |
| `11a1.json` | `44ba617f9c6b25f3144f01f819e9c85fef30b4ec6239cfa875bcde005aae7567` |
| `37a1.json` | `6595e706f2db57c222fcb17d9fddaa867c4072e507dcbae6088bbfdb66e0deb8` |
| `112a2.json` | `086b479d495f05f56bf0134e552487e22e8cc123b86aa64a2a21217798a7e1c0` |

A guarded prototype converted the rational exponential endpoints back to
dyadics and checked representability. In five separate matched profiles its
112a2 quadrature kernel median was 0.196 s, compared with 0.259 s on the
baseline. Keeping the original dyadic endpoints removes that conversion
and its guard. A rational atanh-Horner prototype gave little additional
improvement when combined with dyadic polynomial evaluation in the initial,
host-loaded quadrature microbenchmarks.

The ordinary 11a1, 37a1 and 112a2 inputs omit a trace-hash proof attachment.
A supplemental probe exercised the conditional 37.a1 trace-hash fixture,
the prime-table length check, and reuse of its compiled length theorem.
Verbose tracing of the attached proof produced gigabytes of formatted output
per run, so those timings cannot characterize ordinary trace-hash verification.
The fixture supplies the full coefficient equality as a premise, which also
places independent proof of those coefficients outside this measurement.

Run the tracked benchmark once on baseline `b1490ff` and once on the optimized
revision (evaluator commit `748e5c1`) with the same arguments and pinned dependencies. The script builds
`CertifiedCurves` before timing and records individual samples and witness hashes.

```sh
python3 scripts/benchmark_certify_ec.py --launcher direct --repetitions 7 \
  --profile --cases bare import_only cached_proof 11a1 37a1 112a2 batch \
  --output "/tmp/certify-ec-$(git rev-parse --short HEAD).json"
```

The tracked script collects one separate profile per invocation. Repeat the
invocation to sample profile variation. The paired measurements used the same
sources and direct invocation, selecting the prebuilt project artifacts for each
revision in `LEAN_PATH`.

## November 20 implementation

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
