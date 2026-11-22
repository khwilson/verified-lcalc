# Temporary modularity assumption

On 2026-11-17 the user explicitly authorized a temporary axiom for the missing
curve-to-modular-form connection. This was the project's first exception to its
default prohibition on custom mathematical axioms. A separate, narrow low-rank
forward implication was authorized on 2026-11-22 below.

The axiom is named:

```
VerifiedLcalc.Assumptions.ellipticModularity
```

Its complete proposition is `EllipticModularity`, defined in
`VerifiedLcalc/EllipticCurve/Modularity/Realization.lean`. For every integral
Weierstrass equation with nonzero discriminant it asserts the existence of a
modular realization consisting of:

- A positive level N and a genuine mathlib weight-two cusp form on Gamma_0(N).
- Width one and arithmeticity follow from Mathlib's Gamma_0 API and the
  positive level. First-coefficient normalization follows from coefficient
  matching and the actual curve coefficient at one. These are derived facts,
  not separate fields of the axiom.
- Equality of **every** Fourier coefficient with mathlib's actual
  `WeierstrassCurve.LFunction` coefficient for the rational curve.
- A sign w in {+1,-1} and the rescaled imaginary-axis Fricke identity
  `g(1/t) = w*t^2*g(t)`, where `g(t)=f(i*t/sqrt(N))` and t>0.
- Agreement at smooth primes with TauCeti's mathematical Frobenius trace of the
  input model's reduction. Compatibility with the computable evaluator is proved
  separately.
- For integral models satisfying `gcd(discriminant,c4)=1`, equality of the level
  with the product of distinct primes dividing `|discriminant|`, and equality
  of the sign with `- product_{p | discriminant} (-frobeniusTrace(model,p))`.
  This general semistable compatibility was explicitly authorized by the user
  on 2026-11-17; it is assumed, not proved here.

Outside that semistable criterion, the level and sign remain existentially
supplied by a realization. The assumption
does not identify an arbitrary caller-supplied N or sign with these values. It
does not assume a numerical interval, tail bound, derivative evaluation, BSD,
or any exact vanishing inferred from the precision cutoff.

This packages established modularity and standard identifications, including
the general case beyond semistable curves. The package itself has **not** been
proved in this project. One can replace the axiom by a theorem of the same type
later without changing its consumers.

## Opt-in low-rank BSD implication

On 2026-11-22 the user authorized a separate temporary assumption, isolated in
`VerifiedLcalc.Assumptions.analyticOrder_le_one_implies_finrank`. It covers only
the forward implication for exact analytic order zero or one: for one
nonsingular integral equation and an explicit `ArithmeticModularRealization`,
the order of that realization's L-function at 1 equals the natural-valued
Mordell--Weil rank of the same rational curve. The derived wrappers accept an
exact `ConditionalAnalyticRank` fact and a realization explicitly. This module
is opt-in and is not imported by the default library or `certify_ec`.

Neither converse is assumed. In particular, a catalogue value, an algebraic
rank interval, or numerical smallness cannot supply the exact analytic-order
premise. The converse statements remain conjectural low-rank BSD results and
would require additional hypotheses, such as appropriate Selmer corank and
finiteness of the Tate--Shafarevich group.

## What follows in Lean

`ModularRealization.formL` uses mathlib's `ModularForm.L`. Given any realization,
mathlib proves it is entire and agrees with the actual curve coefficient series
on Re(s)>2. Those general implications are proved in the axiom-free statement
module. Choosing a realization using `ellipticModularity` makes the resulting
curve-specific theorems explicitly depend on that axiom.

`Assumptions/Certificates.lean` supplies separate exact and numerical certificate
interpretations for the continued function at the arithmetic center s=1.
Actual derivative enclosures remain required proof arguments. The exact checker
still requires exact earlier vanishing; numerical smallness remains a separate
conclusion, with a separate explicit hypothesis for any upgrade to exact rank.

`tests/VerifiedLcalcTests/Fixtures/AssumedCurve11.lean` is a worked assumption-dependent certificate:
it obtains an entire continuation matching the actual Euler coefficient series
for 11.a2, checks the realizing form's coefficient at 2 is -2, and identifies
its level as 11 and sign as +1. `CentralIntegral.lean` derives the central
split-Mellin integral from mathlib's Mellin representation and the Fricke field.
This analytic implication itself uses no custom axiom.

`tests/VerifiedLcalcTests/Fixtures/AssumedCurve37.lean` checks the integral model of 37.a1 satisfies
the semistable criterion, computes level 37 and sign -1, and deduces exact
central vanishing and `1 ≤ analyticOrderAt continuedL 1` using the proved
split-Mellin identity. This is a conditional lower bound; it does not claim
exact rank one or use the fixture's expected rank. The exponential-series formula is now derived from the supplied modular
realization with an explicit arithmetic coefficient-bound input. The interval
connection is proved given actual prime-power compatibility. The actual global coefficient bound and Euler-product extraction are now
proved. `tests/VerifiedLcalcTests/Fixtures/AssumedCurve11Central.lean` supplies the eight actual
coefficients and proves exact analytic rank zero, with no further hypotheses
beyond the unchanged axiom. Derivative enclosures remain unfinished.

## Isolation and audit

The default `VerifiedLcalc` import, runtime executables, original certificates
and `Audit.lean` do not import the axiom module. Opt in explicitly:

```
lake build VerifiedLcalc.Certification.NumericalCertification VerifiedLcalcTests.Fixtures.AssumedCurve11 VerifiedLcalcTests.Fixtures.AssumedCurve37
lake env lean AuditAssumptions.lean
lake env lean tests/consumers/AssumedCurve11.lean
lake env lean tests/consumers/AssumedCurve37.lean
lake env lean tests/consumers/AssumedCurve11Central.lean
```

The source of any dependent certificate should retain its assumption imports
and axiom audit. Its results are conditional on the named modularity axiom.
`#print axioms` reports that dependency; it must not be described as an
unconditional proof using only Lean's foundational axioms. The default audit
remains separate so unrelated numerical and exact-demo proofs retain their
original dependency boundary.

The existing elliptic branch of `Artifacts.Subject.Denotes` remains unsupported
in the default axiom-free interface. The opt-in certificate interface provides
the assumption-dependent interpretation instead of altering the old meaning.
The strict LMFDB rank test still requires actual rank outputs and remains
inconclusive until the evaluator supplies the derivative evidence.

## Public FLT source

Anthropic's September 2026 formalization is public at
[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem).
Inspected revision: `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Its [proof guide](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md)
explicitly lists `WeierstrassCurve.modularity_of_semistableModel`, matching
good-prime traces with weight-two cusp-form coefficients. It also explicitly
limits that theorem to semistable models, and does not claim an L-function or
modular-parametrization theorem. The project uses Lean 4.33.1 and mathlib 4.33.0,
so it is not a direct import into this project's Lean 4.36.0-rc2 environment.
No Anthropic proof code has been copied or compiled here. FLT itself is not the
assumed proposition; the general modularity package above is.

## Validation recorded on 2026-11-17

The default build and explicit assumption-module build passed. Fresh replay of
`AssumedCurve11.lean`, its compiled consumer, both cubic certificate checks,
and both audits passed. The guarded assumption audit checks that the general
series-identification theorem has only standard foundational axioms and that
the chosen curve continuation has exactly those plus `ellipticModularity`. The
default audit guards against that axiom leaking into the central numerical
proof. The strict LMFDB rank gate still reports 100 inconclusive cases.

The authorized semistable refinement was checked by explicit level/sign
computations for 11.a2 and 37.a1. The general central split-Mellin theorem has
only standard foundational axioms; the saved 37.a1 rank lower bound has exactly
those plus `ellipticModularity`. The finite-to-canonical coefficient identity
and the elementary `n^3` bound also have only standard foundational axioms.

The conditional regression cache has a separate soundness proof in
`Assumptions/Regression.lean`; `--conditional` labels its axiom dependence.
It never reads the fixture's expected rank as backend input.

The automated semistable batch now generates and kernel-checks certificates,
including conductor/sign and prefix checks, then proves a generated cache
registry sound. Its first run certified 18 of the 100 inputs. The other 82
remain unresolved with explicit reasons. See [BATCH.md](BATCH.md).

The uniform semistable arithmetic engine now identifies every local factor and
coefficient prefix without any custom axiom. The conditional batch has grown
to 70 checked exact rank-zero certificates, retaining exactly the unchanged
modularity axiom. The remaining 30 inputs have explicit unresolved statuses.

The additive reduction extension adds no axioms. All 26 formerly excluded
fixture models have unconditional minimality, additive-factor and coefficient
prefix proofs, guarded by `AuditAdditive.lean`. The new general minimal-model
central certification interface keeps modular level/sign equalities explicit.
At that stage the temporary modularity assumption supplied only the previously
specified semistable compatibility fields; no additive conductor or root-number
formula had been inserted into it.

The 1,100-input expansion retains the same single modularity axiom. Its installed
397 rank-zero certificates and 122 separate negative-sign lower bounds depend
on it. Fast singular traces, the fast-sign equality, invariant minimality and
532 expanded additive coefficient-prefix proofs use only standard Lean/mathlib
axioms. The new audits are `AuditExtended.lean` and `AuditExpandedAdditive.lean`.

## General modularity clarification (2026-11-18)

General modularity for every elliptic curve over Q, including additive reduction,
is authorized. The existing existence proposition already quantified over every
nonsingular input equation; its scope was never restricted by SemistableModel.
The finite conductor/root-number formulas currently implemented were the
semistable specialization. No additional axiom was needed for the new general
certificate interfaces and witness-independence theorem. Local arithmetic
correctness remains separate. See GENERAL_MODULARITY.md and
AuditGeneralModularity.lean.

## Tame arithmetic integration (2026-11-18)

The single permitted `ellipticModularity` axiom now has the stronger type
`GeneralEllipticModularity`, defined in `FullModularityStatement.lean`.
Its witness extends the base realization with standard tame conductor and
root-number compatibility, under proved global minimality and no additive
reduction at 2 or 3. This is a change in assumption **content**, explicitly
using the user's authorization of general modularity with arithmetic
compatibility. Mathematical local epsilon-factor/conductor theory is not
claimed proved here. The executable algorithms' equality to the valuation and
Legendre-symbol formulas is proved without this axiom. Actual numerical
rank certification still uses proved interval enclosures and nonvanishing.
See [TAME_ARITHMETIC.md](TAME_ARITHMETIC.md) and `AuditTame.lean`.

## Wild arithmetic compatibility (2026-11-18)

`ArithmeticModularRealization` additionally has `wildLevel_eq` and
`wildSign_eq`. They identify full mathematical discriminant-prime products
with the modular level/sign under proved global minimality and validated Tate
transcripts. Geometric Tate/Ogg conductor theory and Halberstadt epsilon-factor
compatibility are explicitly **assumed** standard arithmetic compatibility in
the existing authorized general-modularity package. Executable-to-formula
correctness and numerical enclosures remain proved. The axiom's content is
stronger; merely retaining its name does not imply unchanged assumptions.
See [WILD_ARITHMETIC.md](WILD_ARITHMETIC.md) and `AuditWild.lean`.


## Canonical global minimality in arithmetic compatibility

The tame/wild conductor and sign fields now use TauCeti's
`WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ)`, with the usual
Mathlib ellipticity instance. `GloballyMinimalInput` has been deleted.
`globalMinimal_of_witness` proves the canonical predicate directly from the
validated finite witness by applying the minimality criteria to localizations.
The numerical prefix theorem independently uses `minimal_of_witness` over
completions. No localization/completion minimality equivalence is included in
the modularity axiom or used as an unproved bridge. The existing authorized
standard conductor/sign compatibility is now stated over the canonical global
minimality predicate.
