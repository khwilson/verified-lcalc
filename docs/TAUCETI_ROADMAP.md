# Upstream theorem roadmap for verified elliptic L-functions

Audit date: 2026-11-19. This is a proposal for mathematical upstream work, not a claim that the current modularity assumption has been eliminated. Start with the [arithmetic plan](roadmaps/ELLIPTIC_LOCAL_ARITHMETIC.md) and [analytic plan](roadmaps/MODULAR_LFUNCTION_EVALUATION.md) for proposed interfaces and PR acceptance criteria.

## Evidence and reproducibility

The 2026-11-19 source audit used the versions below. See the
[build guide](BUILD.md) for active dependencies and the
[EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md) for the later
TauCeti declaration review.

| Source | Inspected revision | Scope and limitation |
| --- | --- | --- |
| verified-lcalc | implementation commit `8f5205e`, plus the current per-curve precision interface | Existing proof sources; this audit did not run Lean or Lake. |
| mathlib | `3440367ed1804626334f13a3a534a9cbb3385a59` | Local `../mathlib4`; project Lean `v4.36.0-rc2`. |
| TauCeti | `d01c9825761c7e6168457c383458afa8668196a7` | Clean local checkout `../Igusa/memory/upstream/TauCeti`; Lean `v4.35.0-rc3`. An older pinned snapshot, not a current-HEAD audit. |
| Selected TauCeti multiplicativity port | `0642eae29e0a59ef798d04de325386445906e755` | See [port provenance](../VerifiedLcalc/Upstream/TauCeti/PROVENANCE.json). This newer source used mathlib `048fffa1dbcd080d3058fab41d8c188168595c22`; a full integration of that dependency graph was not verified. |
| Ledvinka exponential port | mathlib PR 45193, head `9c80a26d5b6a5b4ec14d6db0aba596463c6b281f` | [Local port](../VerifiedLcalc/Upstream/LedvinkaExponential.lean). The earlier Nov. 17 audit reported closed/unmerged; live PR status was not rechecked for this roadmap. |

The public [TauCeti roadmap](https://github.com/TauCetiProject/TauCetiRoadmap) was consulted on the audit date. Its `main` pages are moving documents, not pinned proof evidence. No claim here that a theorem is absent from every current branch or PR follows from a search of the older local snapshot. Before opening an upstream PR, repeat the declaration search and compile against the target revision. The local `tauceti-framework` directory contains automation infrastructure, not the elliptic-curve theorem library. Earlier LeanBridge reconnaissance was partial and is not evidence of an integrated dependency.

## Ownership and current status

“Locally proved” below means a proof exists in this repository, inspected as source in this audit. It does not mean its proposed generalized replacement has been compiled upstream. Assumption-dependent conclusions must retain that dependency until the relevant mathematical bridge is proved.

| ID | Reusable result family | Present status | Proposed owner | Priority |
| --- | --- | --- | --- | --- |
| M1 | Prime-power extraction from coprime arithmetic Euler products | Locally proved, `EulerProduct.lean` | Mathlib arithmetic functions | First PR |
| M2 | DVR minimality from small discriminant / c4 / c6 valuation | Locally proved | TauCeti elliptic curves, Mathlib-track | First PR |
| M3 | Finite-field point counts under field equivalence; minimal-reduction local-factor adapters | Locally proved | TauCeti elliptic curves | First wave |
| M4 | Rational-place residue cardinality and EC L-function prime-power coefficients | Locally proved using selected TauCeti ports | TauCeti EC L-function | After M1/M3 |
| M5 | Bad-reduction trace bound, recurrence, explicit `n^3` global coefficient bound | Locally proved | TauCeti EC L-function | After M4 |
| T1 | Typed Tate reduction transcript, transformations, algorithmic symbol/exponent | Finite checks and arithmetic path correctness proved locally; complete algorithm and geometric interpretation not proved | TauCeti elliptic curves | Design next |
| T2 | Geometric conductor = algorithmic conductor, especially at 2 and 3 | Explicitly assumed by current arithmetic modular realization | TauCeti local arithmetic / conductor theory | Long term |
| T3 | Local epsilon/root number = finite wild-root formula | Formula implementation checked; geometric identity assumed | TauCeti local L-functions | Long term |
| T4 | Arithmetic modularity normalized by actual conductor, coefficients and sign | Authorized general modularity package assumed | Separate global modularity project | Long term |
| A1 | Continuation uniqueness adapter for modular realizations | Locally proved; TauCeti already has general entire-extension uniqueness | Reuse TauCeti API; keep curve adapter here | Small integration |
| A2 | Central Mellin split and exponential series for weight-two forms | Locally proved with a realization supplied as an argument | Mathlib generic split; TauCeti modular forms | First analytic PR |
| A3 | First derivative as log-weighted upper Mellin integral | Locally proved with negative sign | TauCeti modular forms | After A2 |
| A4 | Higher log-moment derivatives and quantitative tails | First derivative/tail available; general higher-order family not implemented | Mathlib Mellin analysis / TauCeti modular forms | Next analytic milestone |
| N1 | Rational/dyadic exp/log inclusion rules | Local soundness proofs; exp derives from attributed Ledvinka port | Mathlib interval numerics, coordinate with author | Parallel upstream work |
| V1 | Small numerical derivatives imply exact zeros | Only with an explicit curve-specific separation or exact-vanishing hypothesis | Open arithmetic research; conditional interface here | Never silently infer |

Source paths, exact statement examples and dependencies are in the two detailed plans. Existing [elliptic-curve](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/EllipticCurves/README.md) and [modular-form](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/ModularForms/README.md) roadmaps already own the surrounding theory. Propose focused additions to those workstreams rather than another competing foundations library.

### Current release update for local reduction

The project now pins TauCeti `e0e414ce57522ba17560057ad0d7f2edab91bf0c`.
It includes the canonical `WeierstrassCurve.reductionSymbol` and
`reductionSymbol_eq_I_iff` for good and multiplicative reduction.
`forall_reductionSymbol_ne_I_iff` characterizes the additive family.
The project specializes these to a checked minimal integral equation at
a rational prime. Certifying a specific additive symbol requires a bridge
from supplied finite transcripts to TauCeti's `IsTateTerminal`.
[Release reduction APIs](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/TateAlgorithm/Reduction/Curve.lean#L149-L197)

The same release defines the intrinsic Tamagawa number on the completed
field. Its `tamagawaNumber_eq_tateLocalIndex` theorem compares that number
with the algorithmic local index given a terminal transcript and the stated
local-ring hypotheses. The source does not supply an intrinsic local epsilon
factor through this API. The project's current modularity fields constrain
the global sign product.
[Release Tamagawa comparison](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Tamagawa/Local.lean#L139-L156)

## Assumption boundary

The current custom axiom is `VerifiedLcalc.Assumptions.ellipticModularity`. Its type, [GeneralEllipticModularity](../VerifiedLcalc/EllipticCurve/Modularity/ArithmeticRealization.lean), supplies an `ArithmeticModularRealization` for every nonsingular input equation over Q. This includes modular-form existence, coefficient matching and arithmetic normalization; it is not merely semistable FLT-era modularity.

In particular `wildLevel_eq` and `wildSign_eq` identify the level and global sign with computations from a valid wild transcript. Proving that transcript follows integer arithmetic rules does not prove those fields. T2, T3 and the global normalization part of T4 are the missing bridges. Tame compatibility is also an explicit field of the package. M1–M5 improve reusable unconditional arithmetic, but do not by themselves remove this axiom.

The new [curve-specific precision interface](../VerifiedLcalc/Assumptions/Precision.lean) addresses a different issue. A fixed cutoff, derivative convention and a checked enclosure can support a numerical observation. A lower bound on analytic rank additionally needs exact vanishing, or a proved/assumed nonzero-derivative gap exceeding the cutoff. Those hypotheses belong to exactly that curve and claim; they do not follow from general modularity. See V1 in the analytic plan. Exact rank-zero and rank-one certificates use nonvanishing and the functional equation, without a tolerance-to-zero inference.

## Proposed delivery sequence

1. **Extraction PRs:** M1 and M2 independently; M3 where the current upstream API lacks the corresponding invariance lemma. Preserve existing namespaces and minimize new imports. Acceptance: generic statements, no artifact types, no custom axioms, proofs compile on the chosen target pin.
2. **Arithmetic integration:** M4 then M5, with a Q-specific coefficient theorem and explicit scope. Replace the local proof bodies with upstream adapters only after downstream certificate conclusions and axiom audits agree.
3. **Analytic integration:** A1 adapter using existing uniqueness; A2 generic weight-two theorem; A3 derivative formula. Acceptance: supplied cusp form and hypotheses, with no elliptic-modularity axiom in the generic theorems.
4. **Tate specification:** agree T1's typed output and algorithmic meaning with the existing elliptic roadmap. Separate soundness, exhaustiveness, termination, and change-of-equation invariance. Publish T2/T3 dependency contracts before promising axiom removal.
5. **Higher-rank evaluation:** A4 and certified integration extend numerical coverage. Keep V1 as an explicit hypothesis until a separate mathematical argument discharges it. Benchmarking more curves does not discharge V1.

Each upstream PR should record the target Lean/mathlib/TauCeti commits, originating local declarations, licensing provenance, and a downstream replacement experiment. The decisive regression is semantic: the same witness yields the same statement and approved axiom set, including any explicit per-curve hypothesis. Timing alone is not an acceptance test.

## Curve representation at the public boundary

The source audit above predates the public representation migration. The current
Lean interface uses Mathlib’s `WeierstrassCurve ℤ`, with its map to ℚ and fields
`a₁`, `a₂`, `a₃`, `a₄`, `a₆`. The former `Artifacts.CurveEquation` was a
five-integer runtime record, not a different mathematical curve. Upstream APIs
should use the existing Weierstrass-curve type. JSON can remain an external wire
format; it does not require another public mathematical record. Migration build
results are reported separately from this pinned-source audit.

## What stays in verified-lcalc

`certify_ec`, witness JSON, command elaboration, stable theorem names, certificate manifests, optional search, `.olean` packaging and validation benchmarks are project infrastructure. They should consume upstream mathematics. An imported `.olean` is tied to a compatible Lean/dependency environment; this roadmap does not claim cross-version binary proof portability or a kernel attestation from a file hash.

Curve labels, LMFDB imports, raw numerical cutoffs and policy-specific “numerical rank” terminology are also application concerns. Generic analytic-order lemmas can go to Mathlib; no upstream theorem should silently equate a precision policy with exact vanishing.


See [the FLT modularity comparison](FLT_MODULARITY.md) before replacing the
current classical realization package with a Galois/Hecke formulation. The
restricted FLT definition is not a drop-in replacement for additive curves.


The concrete extracted modules and submission-sized entries are in
[TAUCETI_BACKLOG.md](TAUCETI_BACKLOG.md); the later full-source interface review
is in [INTERFACE_REUSE_AUDIT.md](INTERFACE_REUSE_AUDIT.md).
