# Local reduction and Tate-algorithm components

This directory groups the local arithmetic intended for eventual upstream work.
Lean declaration namespaces stay `VerifiedLcalc.EllipticCurve`; imports now use
`VerifiedLcalc.EllipticCurve.Tate.*`.

| Modules | Role |
| --- | --- |
| `AdditiveArithmetic` | Minimality criteria from discriminant valuations, and their rational-curve applications. |
| `InvariantMinimality` | Minimality from the valuations of `c₄` and `c₆`. |
| `TwoAdicMinimality` | The integral `c₄` valuation gap at two and the `v₂(c₄) = 6` minimality criterion. |
| `TameCore`, `TameArithmetic` | Computable tame reduction data and its proved arithmetic interpretation. |
| `WildTateCore` | Integral transformations, divisibility tests, candidate generation, and checked Tate transcripts at two and three. |
| `WildArithmetic` | Arithmetic meaning of transcript checks, valuations, characters, and local formulas. |
| `WildRootCore` | Wild root-number tables and their evaluation; related local arithmetic, not a stage of Tate's algorithm. |

The minimality criteria are standalone theorems, not claims to implement every
stage of Tate's algorithm. Candidate generation is separate from transcript
validation; an unsuccessful bounded search does not prove a model has no valid
transcript. The currently checked transcripts do not yet prove the geometric
Tate/Ogg or local epsilon-factor compatibility. Those remain explicit content
of the authorized modularity package, as documented in
[`docs/roadmaps/ELLIPTIC_LOCAL_ARITHMETIC.md`](../../../docs/roadmaps/ELLIPTIC_LOCAL_ARITHMETIC.md).

For TauCeti integration, separate generic DVR and finite-field theorems from
this project's integral-input adapters and witness infrastructure. The roadmap
lists prerequisites and acceptance criteria. The GPL attribution and license
notice in `WildRootCore` must accompany the root-number table implementation;
the imported TauCeti minimal-model and local-polynomial modules are Apache-licensed.
See the [build guide](../../../docs/BUILD.md) for the upstream revision.
