# Relationship to FLT's modularity formulation

Reviewed on 2026-11-19 through the public source available to the web reader;
this is not an imported dependency or a verified adapter.

FLT's
[`GaloisRep.IsAutomorphicOfLevel`](https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/GaloisRepresentation/Automorphic.lean)
uses Galois representations and quaternionic weight-two Hecke eigenforms.
At good finite places it requires unramifiedness, determinant equal to the
residue norm, and Frobenius trace equal to the relevant Hecke eigenvalue.
The source deliberately restricts the fields, quaternion algebra and levels
for its FLT strategy; this is not an unrestricted elliptic modularity statement.
Its surrounding development also contains unfinished proofs, so copying the
file is not a source of additional checked theorems for this project.

The [blueprint](https://imperialcollegelondon.github.io/FLT/blueprint/ch_overview.html)
explains the totally real, even-degree, definite-quaternion setting and
modularity lifting approach.

Our current assumption is over Q and produces the classical realization needed
by the evaluator. It additionally contains documented conductor/sign
compatibility. It is not FLT's definition or a formal consequence already
proved from it.

A future integration should reuse upstream Galois/Hecke objects and explicitly
prove the bridges to classical cusp forms, all required local Euler factors,
completed L-functions, functional equations and the Fourier/Mellin evaluation
formulas. The restricted FLT level condition cannot simply replace the present
all-reduction-type package. No Galois-to-analytic adapter or broader number-field
modularity axiom is introduced by this comparison.

## Anthropic's classical formulation

The separate Anthropic repository defines
[`WeierstrassCurve.IsModular`](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_FLTPrelim_Modularity.lean)
by existence of an integral model and a normalized weight-two eigenform matching
at common good primes. Its
[`modularity_of_semistableModel`](https://github.com/anthropics/fermats-last-theorem/blob/main/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean)
requires a nonzero discriminant and semistability, without an explicit minimality
hypothesis. This matches the semistable scope needed for that FLT proof.

Our modularity axiom likewise quantifies over every nonsingular integral equation
without a minimality premise. Minimality is required by the later compatibility
formulas that read invariants from the supplied model. `GloballyMinimalInput` is
a local predicate asserting Mathlib minimality at each rational-prime completion, discharged
from checked witnesses. Nonminimal models can have artificial bad reduction;
their raw reduction counts need not give the intrinsic Euler factors. The
semistable-model hypothesis in the cited theorem already excludes that scaling
problem. Good-prime modularity matching alone does not supply our bad-prime
factors, precise level, sign or analytic-normalization bridges.
