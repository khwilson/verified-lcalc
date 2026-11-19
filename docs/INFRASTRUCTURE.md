# Infrastructure audit: TauCeti and David Ledvinka's intervals

Inspected on 2026-11-17. This records reusable mathematical infrastructure and
its limits; it does not claim that the entire analytic-rank backend exists.

## Integration completed in this workspace

Selected TauCeti arithmetic proofs are now ported and kernel-checked against
our existing mathlib pin. See
[the port provenance](../VerifiedLcalc/Upstream/TauCeti/README.md) and
[the integration status](INTEGRATION.md). The default library imports the
axiom-free arithmetic adapter. The modularity-dependent evaluator interface
remains opt-in. This supersedes the earlier source-inspection-only status.

## Global coefficient integration and first rank-zero certificate

The completion residue-field proof is now also ported, bringing the selected
TauCeti subset to ten modules/excerpts. Our checked adapters prove rational
prime-ideal norm uniqueness, formal Euler-product prime-power extraction and
an actual-curve global n^3 coefficient bound without a modularity assumption.
The independent input-model identification is no longer needed for the
infinite tail. The concrete 11.a2 prefix is proved from the existing modular
realization's good-prime fields, the actual local recurrence and
multiplicativity. Its saved eight-term payload now proves exact rank zero
conditional only on the unchanged modularity axiom. See
[INTEGRATION.md](INTEGRATION.md) for the current boundary and regression mode.

## Upstream refresh: 2026-11-17

The earlier TauCeti findings below used the older local checkout. A fresh GitHub
source inspection found substantially more reusable infrastructure at current
commit `0642eae29e0a59ef798d04de325386445906e755` (2026-11-17).
This revision uses our Lean version, `v4.36.0-rc2`, but a different mathlib
revision, `048fffa1dbcd080d3058fab41d8c188168595c22`. It has not yet been
added as a dependency or built/audited in this project.

| Obligation | Available source theorem or infrastructure |
| --- | --- |
| Local Frobenius bounds | `EllipticCurve/HasseBound.lean`: `WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card` and `hasse_bound`, using actual Weierstrass curves and point counts. The trace theorem also handles singular reductions. |
| Good and bad local polynomials | `EllipticCurve/LocalPolynomial.lean`: `localPolynomial_eq_of_hasGoodReduction` and `localPolynomial_eq_of_not_hasGoodReduction`; the latter identifies the linear factor using the minimal reduction's trace. We still need to connect our finite model to that minimal reduction. |
| Global multiplicativity | `EllipticCurve/LFunction/Basic.lean`: `isMultiplicative_localEulerFactor`, `isMultiplicative_LFunction`, `LFunction_apply_one`. This supplies general arithmetic-function infrastructure, not yet our executable-prefix identification. |
| Analytic continuation for a supplied cusp form | Already in mathlib: `CuspForm.differentiable_L`, `Λ_eq_mellin`, `hasSum_L`. TauCeti's `ModularForms/LFunction/Basic.lean` connects this with `LSeries` and continuation interfaces. |
| Level-N functional equation and sign | `ModularForms/LFunction/FunctionalEquation.lean`: `frickeCompletedL_functional_equation`, entire completion, and the normalization `frickeCompletedL_eq_cpow_mul_Λ`. `LFunction/Sign.lean` specializes to self-dual forms/newforms and proves forced central vanishing. |
| Explicit numerical tail majorant | Hasse plus the local recurrences and multiplicativity should yield our weak polynomial coefficient bound. This final quantitative adapter has not been implemented here. A modular-form big-O bound alone does not provide an explicit numerical constant. |

Pinned sources:

- [Hasse bound](https://github.com/TauCetiProject/TauCeti/blob/0642eae29e0a59ef798d04de325386445906e755/TauCeti/AlgebraicGeometry/EllipticCurve/HasseBound.lean)
- [Local polynomial identification](https://github.com/TauCetiProject/TauCeti/blob/0642eae29e0a59ef798d04de325386445906e755/TauCeti/AlgebraicGeometry/EllipticCurve/LocalPolynomial.lean)
- [L-function multiplicativity](https://github.com/TauCetiProject/TauCeti/blob/0642eae29e0a59ef798d04de325386445906e755/TauCeti/AlgebraicGeometry/EllipticCurve/LFunction/Basic.lean)
- [Fricke/Mellin functional equation](https://github.com/TauCetiProject/TauCeti/blob/0642eae29e0a59ef798d04de325386445906e755/TauCeti/NumberTheory/ModularForms/LFunction/FunctionalEquation.lean)
- [Central sign](https://github.com/TauCetiProject/TauCeti/blob/0642eae29e0a59ef798d04de325386445906e755/TauCeti/NumberTheory/ModularForms/LFunction/Sign.lean)

The selected files contain proof bodies rather than `sorry` stubs. This source
inspection is not a transitive dependency or kernel-build audit.

For our deliberately weak bound `|a_n| <= n^3`, full Hasse/Weil estimates
are stronger than necessary. There is an elementary route: counting affine
solutions gives `|a_p| <= p^2`; the local recurrence with `|q| <= p` then
gives `|a_(p^k)| <= p^(3*k)` by induction, and multiplicativity gives the
global bound. This derivation is now proved in `EllipticCurve/Bounds.lean`. It does not remove the need to identify
the model factors with the actual curve's factors.

The remaining large bridge is a theorem associating the actual rational
elliptic curve with a weight-two cusp form and identifying its coefficients and
level. Targeted source searches did not locate such a general modularity theorem
in current TauCeti. Its `EllipticCurve/ModularForm.lean` concerns invariant
polynomials in Weierstrass coefficients, not the modularity theorem. Its BSD
statement still takes an analytic continuation as an argument. The exact
exponential central-value identity also needs to be derived from the available
Mellin/Fricke results, with justified termwise integration.

Other relevant projects:

- [Chris Birkbeck's AINTLIB HasseWeil](https://github.com/CBirkbeck/AINTLIB/blob/c3415f32a313e19ace43e05479aeaa0d56ca287a/projects/HasseWeil/HasseWeil/HasseBound.lean)
  provides `HasseWeil.WeilPairing.hasse_bound` for Weierstrass curves over finite
  fields. TauCeti's source records this development as provenance. AINTLIB also
  contains the `LeanModularForms` Fricke-functional-equation development cited
  by TauCeti.
- [AxiomMath's release](https://axiommath.ai/research/the-weil-conjectures-formalized-in-lean/)
  and its [Weil repository](https://github.com/AxiomMath/Weil) target the general Weil
  conjectures over finite fields, including Frobenius weight estimates. This
  is relevant to local coefficient bounds, but a finite-field zeta functional
  equation is not the global complex functional equation of an elliptic curve
  over Q. It does not by itself supply the modularity bridge. Its toolchain
  and Stacks dependencies differ from this project; a smaller Hasse theorem is
  the more direct input for this evaluator.

## TauCeti: earlier local checkout

The inspected local mathematical checkout is
`../Igusa/memory/upstream/TauCeti`, clean at commit
`d01c9825761c7e6168457c383458afa8668196a7` (2026-10-02), using Lean
`v4.35.0-rc3`. Our project uses `v4.36.0-rc2`. The upstream `main/lean-toolchain`
viewed on the web reports `v4.36.0-rc2`, but attempts to retrieve the current main
commit/source tree failed; the mathematical findings below are scoped to the
inspected local pin. The automation repositories under `../tauceti-framework`
are not the mathematical library.

Useful files at the inspected pin:

| Module under `TauCeti/` | Infrastructure and relevance |
| --- | --- |
| `AlgebraicGeometry/EllipticCurve/PointCount.lean` | Projective equation count includes all affine solutions and infinity, including a singular point at bad reduction. It proves agreement with mathlib's point type for smooth models. Our executable uses the same counting convention. |
| `AlgebraicGeometry/EllipticCurve/SingularPointCount.lean` | Counts singular models; obtains traces 1, -1, and 0 for split nodes, nonsplit nodes, and cusps. |
| `AlgebraicGeometry/EllipticCurve/LocalPolynomial.lean` | Connects these traces with mathlib's local Euler polynomial of the **minimal** model, at good and bad reduction. This is directly relevant to completing the global coefficient backend. |
| `AlgebraicGeometry/EllipticCurve/Affine/FinitePoint.lean` | Finiteness of the curve-point type over a finite ring. |
| `NumberTheory/LSeries/EntireExtension.lean` | `LSeries.HasEntireExtension`, uniqueness, and interfaces for entire functions extending a coefficient Dirichlet series. Existence for a particular elliptic curve is still a separate obligation. |
| `NumberTheory/ModularForms/LFunction/Basic.lean` | Coefficient-series/entire-function identifications and continuation uniqueness for cusp forms. |
| `NumberTheory/ModularForms/Newforms/AnalyticInvariants.lean` | Analytic rank of a newform; finite order and independence of the chosen entire continuation. |
| `Analysis/SpecialFunctions/IncompleteGamma.lean` | Analytic lower incomplete gamma, identities, and monotonicity; not a certified executable interval evaluator. |

Pinned source links:

- [Point counts](https://github.com/TauCetiProject/TauCeti/blob/d01c9825761c7e6168457c383458afa8668196a7/TauCeti/AlgebraicGeometry/EllipticCurve/PointCount.lean)
- [Local Euler polynomials](https://github.com/TauCetiProject/TauCeti/blob/d01c9825761c7e6168457c383458afa8668196a7/TauCeti/AlgebraicGeometry/EllipticCurve/LocalPolynomial.lean)
- [Entire extensions](https://github.com/TauCetiProject/TauCeti/blob/d01c9825761c7e6168457c383458afa8668196a7/TauCeti/NumberTheory/LSeries/EntireExtension.lean)
- [Newform analytic ranks](https://github.com/TauCetiProject/TauCeti/blob/d01c9825761c7e6168457c383458afa8668196a7/TauCeti/NumberTheory/ModularForms/Newforms/AnalyticInvariants.lean)

In the inspected checkout, targeted searches did not find a theorem producing a
weight-two newform for an arbitrary rational elliptic curve and identifying all
its Euler coefficients, nor a certified interval evaluator for the required
transcendental expressions. This is a search result, not a claim about every
current TauCeti theorem. The existence of a newform analytic-rank definition by
itself does not supply the curve-to-newform connection or central value bounds.

No TauCeti dependency has been added: blindly adding this older checkout would
introduce a toolchain/mathlib mismatch. Before reusing it directly, choose a
compatible immutable upstream pin and audit the selected modules' dependencies.
No TauCeti proof source had been copied at that earlier audit stage; the selected ports described above were added subsequently.

## David Ledvinka: inclusion and dyadic intervals

This work is already present in our pinned mathlib revision
`3440367ed1804626334f13a3a534a9cbb3385a59`; no external package is needed.
Relevant authored modules:

- `Mathlib/Tactic/Inclusion/Extension/Interval/Basic.lean`:
  `Inclusion.Interval`, including optional unbounded endpoints, arithmetic, and
  containment theorems.
- `Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Basic.lean`:
  interpretation of dyadic intervals in ℝ and proved arithmetic operations.
- `.../IntervalDyadicReal/Rational.lean`: outward-rounded rational enclosures,
  precision control, rational balls, and exact rational-division enclosures.
- `.../IntervalDyadicReal/Tactic.lean`: the `dyadic_interval` tactic, including
  precision and binary-splitting options.

[The pinned tactic source](https://github.com/leanprover-community/mathlib4/blob/3440367ed1804626334f13a3a534a9cbb3385a59/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Tactic.lean)
and its associated files explicitly attribute David Ledvinka. Git history also
records his multiplication, absolute-value, power, and integer extensions.

`VerifiedLcalc/Numerics/Dyadic.lean` now provides a proved adapter from four
bounded dyadic endpoints to our rational complex certificate rectangle. The
containment theorem identifies its interpretation with Ledvinka's interval
memberships. It also contains kernel-checked uses of `dyadic_interval` for a
rational cast and a polynomial bound. The default proof route is used; no native
verification option is enabled.

The pinned inclusion tree itself has no exp/log/gamma extension. Searching
Ledvinka's unmerged work found:

- [PR #45193](https://github.com/leanprover-community/mathlib4/pull/45193),
  branch `inclusion-exp`, head `9c80a26d5b6a5b4ec14d6db0aba596463c6b281f`:
  proved dyadic exponential bounds and an `exp_mem` inclusion rule. GitHub's API
  reports the draft closed and unmerged. We ported this source to our pin and
  checked its proofs, preserving the Apache license. See
  [source provenance](../VerifiedLcalc/Upstream/README.md). The executable
  definitions live in a Std/Init core; proofs use mathlib separately.
- [PR #40107](https://github.com/leanprover-community/mathlib4/pull/40107),
  branch `interval_arithmetic`, head
  `54e8932b9e3f12ec3379acc6761d2253c01c6705`: older exp/log implementations,
  but `Interval.dyadic_exp_inclusion` and `Interval.dyadic_log_inclusion`
  both contain `sorry`. This draft is also closed and unmerged. We did not
  import its unproved logarithm implementation.
- No gamma interval evaluator was located in the inspected PRs or author
  searches. This does not establish that no other branch exists.

`Numerics/Exponential.lean` proves the adapter to rational rectangles and
kernel-checks positive, negative, and interval exponential examples.
`Numerics/ExpSum.lean` proves signed finite-sum bounds and their extension by
an independently proved tail estimate. It includes a rank-zero theorem for an
analytic function whose actual central real part satisfies that estimate.
The theorem does not provide an elliptic-curve evaluation formula or tail bound.
The compiled scalar demo is `lake exe exp-enclosure -1 0 24`, with exact rational
endpoints. Numerical examples use kernel checking, never native verification.

## Mathlib elliptic L-series

The current mathlib source already has
`Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`, defining local
polynomials, formal Euler coefficients, and a coefficient `LSeries`.
The earlier project search missed this file. `Mathlib/NumberTheory/LSeries/Basic.lean`
explicitly says that `LSeries` is the convergent sum, with a default zero otherwise;
it is **not** the analytic continuation. Evaluating that definition at the center
would not establish analytic rank. Central evaluation needs an entire
continuation and a proved connection to the curve's coefficients.

The targeted cache fetch attempted in this session failed because
`cache.mathlib.org` could not be resolved. The implemented arithmetic and interval
proofs reuse already-available mathlib artifacts; they do not import the large
elliptic `LFunction` dependency tree into the executable.
