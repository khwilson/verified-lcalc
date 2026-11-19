# Extracted TauCeti candidates

These are compiled proofs used by the backend, not copied prototypes or assumed
interfaces. Declarations use the `WeierstrassCurve` namespace. The source bodies
were extracted from this project's arithmetic adapters; the backend imports them.

| Module | Results | Suggested destination |
| --- | --- | --- |
| `Minimality` | Minimality from discriminant, c4 or c6 valuation bounds. | TauCeti `MinimalModel/Basic.lean`, eventually Mathlib. |
| `TwoAdicMinimality` | Integral c4 valuation gap when 2 is a uniformizer; minimality at c4 valuation six. | TauCeti `MinimalModel/` adjacent to the generic criteria. |
| `PointCount` | Computable finite-field count, equality with the existing mathematical count, and field-isomorphism invariance of counts/traces. | TauCeti `PointCount.lean`. |

The minimality modules import Mathlib and each other only. `PointCount` imports
the pinned TauCeti point-count port; an upstream patch should replace that
project-specific import path with the canonical TauCeti import. No witness,
JSON, LMFDB, precision-policy or modularity-assumption dependencies belong here.

`tests/UpstreamCandidates.lean` audits all eight public correctness/invariance
results for standard Lean axioms only. The two-adic hypotheses include the
normalization `v(2) = exp(-1)`; do not silently generalize them to ramified
extensions where 2 is not a uniformizer.

See [the prepared backlog](../../../docs/TAUCETI_BACKLOG.md) for prerequisites,
acceptance criteria and the separate, still-unproved bridge work. No upstream PR
or external issue has been submitted by this extraction.
