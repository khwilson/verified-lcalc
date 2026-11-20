# EllipticCurve file-by-file reuse audit

Audit baseline: local commit `9f7b5e9`; Mathlib
`3440367ed1804626334f13a3a534a9cbb3385a59`; complete TauCeti checkout
`d01c9825761c7e6168457c383458afa8668196a7`, with the selected newer LFunction
ports documented in `VerifiedLcalc/Upstream/TauCeti/PROVENANCE.json`.
This covers every Lean source in `VerifiedLcalc/EllipticCurve/`, recursively.
Findings concern these pins, not uninspected branches or future library work.

The rows below were recorded before applying the queue. A mathematical API's
existence does not imply that it supplies executable kernel-reducible code or
has the hypotheses needed by an input-model checker. In particular Mathlib's
polynomial ring operations are noncomputable at this pin. Use polynomials as
the specification and integer coefficient routines as the executable evaluator.

## Queue

| ID | Cleanup | Exact reused interface | Status |
| --- | --- | --- | --- |
| E01 | Delete `ModelEulerFactor` and its tautological correctness lemmas; table ordinary prime-power coefficient functions instead. | Mathlib `WeierstrassCurve.localPolynomial`, `PowerSeries.invOfUnit`; the existing minimal-reduction bridge supplies their meaning. | Applied and checked. |
| E02 | Delete `localSeries` as a second inverse-series specification; state coefficient correctness against `PowerSeries.invOfUnit` directly. | `PowerSeries.invOfUnit_mul`, inverse uniqueness; retain the proved executable quadratic recurrence. | Applied and checked. |
| E03 | Delete the second finite-field trace-bound proof and specialize the shared result at its sole consumer. | Shared `frobeniusTraceFinite_abs_le_square`, `frobeniusTraceFinite_eq_frobeniusTrace`, `Fintype.ofFinite`. | Applied and checked. |
| E04 | Delete handwritten integral translation formulas and their reflexive correctness wrapper. | Mathlib `WeierstrassCurve.VariableChange` action and `variableChange_Δ`. | Applied and checked. |
| E05 | Delete `TateDiv` and its reflection lemma. | Mathlib integer divisibility and its decidable instance. | Applied and checked. |
| E06 | Delete handwritten quadratic character/Legendre implementations and duplicated specs. | `legendreSym`, `ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'`; retain only required dispatch/prime guards. | Applied and checked. |
| E07 | Delete the private induction about prime membership in a product. | Mathlib `mem_list_primes_of_dvd_prod`, `Nat.prime_iff`. | Applied and checked. |
| E08 | Remove unused definition-unfolding correctness wrappers. | Definitions themselves and substantive existing soundness theorems. | Applied and checked. |
| E09 | Delete the bespoke `InverseEulerCoefficients` predicate and unused uniqueness induction. | Mathlib `LinearRecurrence.IsSolution`/uniqueness exists; use the stronger canonical inverse-series specification already supplied by E02 and retain only the operational recurrence lemma. | Applied and checked. |
| E10 | Remove the `gamma0` wrapper and redundant arithmeticity, width-one and normalization fields from `ModularRealization`. | Mathlib coercion for SL₂ subgroups, `instFiniteIndexGamma0`, arithmetic-subgroup instance, `strictWidthInfty_Gamma0`; normalization follows from coefficient matching and `LFunction_apply_one`. | Applied and checked. |
| E11 | Delete `GloballyMinimalInput` and use TauCeti global minimality in arithmetic compatibility. | `WeierstrassCurve.IsGlobalMinimal`, localization fraction-field/DVR instances and `integers_valuation_localizationAtPrime`; replay the proved criteria over localizations. | Applied and checked. |

## Root files, inspected individually

| File | Existing API checked and disposition |
| --- | --- |
| `Arithmetic.lean` | Uses Mathlib curves/base change, decidable primality, and shared finite-ring count/trace. `localPair` is an executable recurrence, not a second curve API; retain with correctness. E08 removes its unused reflexive pair wrapper; E09 removes the duplicate recurrence specification/uniqueness induction. |
| `BadPrime.lean` | TauCeti `nodePolynomial`, singular trace trichotomy, and Mathlib quadratic splitting are already used. Keep root-search/evaluation bridges: the canonical polynomial operations are noncomputable. No full drop-in executable root search was found. |
| `BadPrimeCore.lean` | `nodeValue` evaluates TauCeti's noncomputable node polynomial using integers; it has the semantic proof in `BadPrime`. Keep as evaluator, not as a new tangent-polynomial specification. |
| `Bounds.lean` | Mathlib finite counting, factorization, product/power estimates already reused. E01 removes the record-based bound/interface. The loose recurrence majorant is project-specific; no exact upstream theorem found. |
| `Central.lean` | Uses Mathlib `HasSum`, analytic order, interval membership and actual tail evidence. Payload assembly is specific to this checker; retain. No upstream central numerical payload type found. |
| `CentralCore.lean` | Pi constants are rational endpoints justified by Mathlib's decimal bounds; `Nat.sqrt` supplies integer roots. Finite payload/evaluator remains. E08 removes bare definition-unfolding wrappers. |
| `CentralFinite.lean` | Already uses `Real.pi_gt_d20`, `pi_lt_d20`, `Nat.sqrt_le'`, `lt_succ_sqrt'`. Scale enclosure and list-index coupling are new glue. `rationalExpSumBounds_correct` cannot replace indexed coupling verbatim: equal terms can have different indices. |
| `CentralTail.lean` | Already uses Mathlib geometric summation, shifted HasSum and norm bounds. The shifted-square majorant is extra quantitative glue, not a duplicate geometric-series theorem. |
| `CoefficientCore.lean` | E01. Replace the custom Euler-factor record with ordinary cached coefficient evaluators; retain `padicValNat` and list aggregation. Do not execute the noncomputable canonical polynomial API. |
| `Coefficients.lean` | E01. Its proof uses Mathlib `Nat.multiplicity_eq_factorization` and finite prime-factor support; retain this executable-to-mathematical bridge. |
| `Correctness.lean` | Already reduced to five backend-specific Boolean/input adapters; canonical count and trace correctness are reused. No duplicate mathematical Weierstrass definition remains. |
| `Derivative.lean` | Mathlib interval integrals, `HasSum`, logarithms and exponential theory are reused through numerical soundness. This payload enclosure has no corresponding upstream evaluator. Retain. |
| `DerivativeCore.lean` | Rational quadrature, tail bounds and witness payloads are executable routines specific to certification. No matching Mathlib/TauCeti numerical derivative evaluator found. |
| `Euler.lean` | E02. Use Mathlib's inverse of the canonical quadratic polynomial as the specification; keep only the recurrence-to-inverse coefficient proof. |
| `EulerProduct.lean` | Mathlib `ArithmeticFunction.ofPowerSeries`, `eulerProduct`, Northcott stabilization exist and are used. TauCeti's analytic `LSeries` Euler products assume summability and do not replace formal coefficient extraction. The coprime-factor extraction glue remains. |
| `GlobalMinimality.lean` | E11. A checked witness proves the canonical localization-based `IsGlobalMinimal` directly. Completion minimality remains separately proved for numerical coefficients; no equivalence axiom. |
| `GlobalBounds.lean` | E03. Bad-reduction trace bound already follows from TauCeti local-polynomial classification. The chosen-minimal-model prime-power recurrence and loose global cube bound remain useful derived results. |
| `GlobalCoefficients.lean` | Mathlib rational ring-of-integers equivalence/ideal norms and TauCeti completion-residue equivalence are reused. Rational-place specialization plus formal Euler-product extraction is extra glue; no exact counterpart found. |
| `MinimalArithmetic.lean` | Already uses extracted generic supplied-minimal-model local-polynomial theorem. Rational completion/residue identification and executable prime-power conversion remain necessary; E01/E02 simplify their representations. |
| `PrefixCore.lean` | A sufficient finite eligibility predicate, not a mathematical semistability or L-function definition. Keep. |
| `RationalPrimes.lean` | Already uses `HeightOneSpectrum.equivOfRingEquiv`, `Int.prime_absNorm`, `Int.ideal_span_absNorm_eq_self`, and quotient norm invariance. Rational specialization is not an alternate prime-ideal theory. Keep. |
| `ReductionArithmetic.lean` | E07. Existing minimality dispatch and witness factorization are project-specific. E11 reuses its finite witness evidence to prove canonical localization minimality separately; numeric completion minimality remains explicit. |
| `ReductionCore.lean` | `ModelReduction` classifies a supplied cubic, including singular inputs; Mathlib geometric reduction predicates require a local field/minimal elliptic curve. Keep dispatcher/witness formats and connect through existing proofs. |
| `Residue.lean` | Already composes `Ideal.quotientEquiv`, `Ideal.quotEquivOfEq`, `Int.quotientSpanNatEquivZMod`, and TauCeti completion-residue equivalence. O_Q quotient is not definitionally `ZMod p`; keep the adapter. |
| `SemistableArithmetic.lean` | Already uses Mathlib Bezout/local-ring unit arguments and TauCeti minimality. Rational supplied-model specialization remains. Intrinsic TauCeti semistability is not the integral gcd criterion on possibly singular models. |
| `TauCeti.lean` | E01/E02. Retain residue-model transport and prime-power/global coefficient bridges; existing Mathlib local polynomial and series definitions remain the specification. |

## Modularity files, inspected individually

| File | Existing API checked and disposition |
| --- | --- |
| `ArithmeticRealization.lean` | The conductor/root-number compatibility fields remain within the authorized modularity assumption. No intrinsic elliptic Artin/Swan-conductor or local epsilon-factor implementation found at the audited pin; generic character conductors do not replace these fields. |
| `Canonical.lean` | Choice from the single authorized modularity axiom is project-specific. Unused projection wrappers can be removed under E08; use realization fields/methods directly. |
| `CentralIntegral.lean` | Already uses Mathlib cusp-form Mellin identity, scaling and Gamma value. TauCeti `CuspForm.L_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul` uses Gamma1 and a normalized operator eigenvector; our Gamma0 pointwise Fricke assumption needs a proved restriction/operator bridge before replacement. |
| `CentralSeries.lean` | Fourier-to-exponential integral glue uses Mathlib sums/integrals and actual-curve coefficient bounds. E01 updates evaluator references. No duplicate convergent central evaluator found. |
| `FastSign.lean` | Execution adapter for the assumed mathematical product via proved singular traces. Keep equality, do not replace mathematical trace with an algorithm in the modularity statement. |
| `FirstDerivative.lean` | Already calls Mathlib `mellin_hasDerivAt_of_isBigO_rpow`, scaling, Gamma differentiability and integration. Scaled-realization and sign cancellation are extra glue. No exact same normalized derivative theorem found. |
| `Fourier.lean` | Already uses Mathlib `ModularForm.hasSum_qExpansion`, periodic qParam, complex-real HasSum and integral maps. Realization-specific scaling/index shifts are extra glue. |
| `Prefix.lean` | Its deliberately restrictive finite criterion is a legacy alternate proof route, not an upstream modularity theorem. E01 updates it; replacing it with `minimal_prefix` would require additional minimality inputs. |
| `Realization.lean` | E10 removes redundant Gamma0 metadata and a duplicate coercion. Actual Mathlib curve coefficients, cusp forms, q-expansion and L function are used. TauCeti newforms use a richer Hecke/Gamma1 package; not interchangeable with the current assumption without an interface bridge. Retain authorized assumption boundary. |
| `RealizationIndependence.lean` | Uses Mathlib analytic continuation uniqueness directly. Equality for two supplied curve realizations is a corollary, not a competing continuation framework. Keep. |

## Tate files, inspected individually

| File | Existing API checked and disposition |
| --- | --- |
| `AdditiveArithmetic.lean` | Existing Mathlib ideal-valuation/divisibility and TauCeti minimal-model criteria are already used. Input-model Boolean reduction bridges remain; E01 updates polynomial interface. |
| `InvariantMinimality.lean` | Uses extracted generic Mathlib/TauCeti-style minimality criteria. This integer-completion specialization is not another invariant/minimal-model definition. Retain. |
| `TameArithmetic.lean` | E06 removes duplicate Legendre correctness proof. E11 removes `GloballyMinimalInput`; arithmetic compatibility now uses canonical localization-based `IsGlobalMinimal`. `tameAtWild` only excludes additive reduction at 2 and 3, not all primes. |
| `TameCore.lean` | E06 removes custom Legendre and square search. Finite conductor/root dispatch has no exact intrinsic elliptic replacement at this pin; geometric interpretation stays assumed. |
| `TwoAdicMinimality.lean` | Uses extracted generic two-adic c4 valuation criterion plus Mathlib completion valuations. Retain only this rational input adapter. |
| `WildArithmetic.lean` | E04/E05/E06 remove translation, divisibility and character duplications. Valuation/transcript-to-mathematical formulas remain distinct from geometric Tate/Ogg/epsilon-factor correctness. |
| `WildRootCore.lean` | E06 uses Mathlib quadratic characters directly. Halberstadt/PARI table organization has no exact upstream replacement; retain GPL attribution and assumed geometric interpretation. |
| `WildTateCore.lean` | E04/E05. Transcript/path checks and bounded untrusted search remain. Polynomial `Separable` and derivative APIs exist, but the finite root tests are not definitionally those predicates: a degree/characteristic/repeated-factor bridge is required before replacing them. No complete Tate algorithm found in the pinned elliptic subtree. |

## Deferred bridges, not automatic deletions

The general TC-04 localization/completion comparison, intrinsic conductor/epsilon factors,
Gamma0-to-Gamma1 normalized Fricke compatibility, and the polynomial-separability
meaning of transcript checks require new theorems. They are not solved by
renaming definitions or importing a similarly named result. Follow-up source
ports need their own dependency/cache and axiom audit. No new axiom is authorized
by this audit.

## Applied changes and supported-input behavior

E01–E10 have been applied. The finite table contains ordinary pairs of primes
and coefficient functions; it has no alternative Euler-factor type. The
canonical inverse-series theorem supplies the evaluator's mathematical
specification and the minimal-model bridge identifies the actual curve factor.
No new local polynomial or generating-series definition was added.

All supplied Tate translations now use Mathlib's `VariableChange` action, and
all weighted divisibility conditions use integer divisibility directly. The
wild root table uses Mathlib's primitive quadratic characters. The tame
additive evaluator validates primality before using `legendreSym`; its
previously unsupported nonprime inputs now return zero. Characteristic-two/
three additive cases are still handled only through the validated wild route.
The local conductor API continues to reject unsupported inputs explicitly.

The generic linear-recurrence machinery was inspected during the follow-up.
The unused custom recurrence predicate and uniqueness induction were deleted;
only the executable recurrence lemma and its stronger inverse-series
correctness theorem remain. No additional recurrence framework is imported
just to recreate an unused wrapper.

The final modularity pass also removes `gamma0`, `arithmetic`, `widthOne` and
the stored `normalized` proof field. The form now lives on Mathlib's coerced
`CongruenceSubgroup.Gamma0`. Positivity of the level supplies `NeZero`, after
which existing finite-index/arithmetic instances and width lemmas apply.
`ModularRealization.normalized` is now derived from coefficient matching and
TauCeti's `LFunction_apply_one`, rather than assumed independently.

## Validation

Completed 2026-11-20. `python3 scripts/check_lean.py` passed on the final
source: production executables/library, compiled certificate examples, test
library, command rejection/rollback, JSON and precision hypotheses, finite
counts, upstream-candidate axiom checks, direct Mathlib regressions, all
arithmetic/analytic assumption audits, and import-only consumers.
`make check test` passed Ruff, formatting, ty and all three Python tests.

A static import scan found no missing project modules and no production import
of the test library. Every one of the 44 elliptic source files has a row above.
The only custom axiom remains `Assumptions.ellipticModularity`; no new axiom or
proof placeholder was introduced. No performance improvement is claimed by
these representation and API changes.

## Canonical global-minimality follow-up

E11 removes `GloballyMinimalInput` rather than renaming its completion-based
body. The arithmetic modularity fields take TauCeti's actual
`IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ)`. A new witness theorem establishes
that predicate directly using the upstream localization/valuation-integers
API and the already proved discriminant, c4, c6 and special two-adic criteria.
The original completion-minimality evidence continues to justify the numerical
coefficient identity. Neither implication between arbitrary localization and
completion minimality is assumed or claimed proved.

The audit now covers 44 files, including `GlobalMinimality.lean`. The canonical
predicate and localization instances are selected upstream excerpts with source
hashes, unchanged theorem namespaces, and retained attribution. The new
regression checks the borderline two-adic model 32.a4, an outside-support prime,
and standard-only axiom dependencies.

The E11 follow-up passed the complete Lean suite, including the new
`tests/GlobalMinimality.lean` regression and axiom audit. Ruff, ty and Python
tests passed as well. The generic localization/completion equivalence remains
open; it is not a premise of the checked-witness integration.
