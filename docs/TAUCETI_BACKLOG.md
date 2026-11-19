# Prepared TauCeti backlog

Source audit: TauCeti `d01c9825761c7e6168457c383458afa8668196a7`, Mathlib
`3440367ed1804626334f13a3a534a9cbb3385a59`. This is a local backlog for upstream
review; it does not claim external issues or pull requests were created.

## TC-01 — extracted generic minimality criteria

Status: proved source, extracted into
[`Minimality.lean`](../VerifiedLcalc/UpstreamCandidates/TauCeti/Minimality.lean).

Declarations: `WeierstrassCurve.minimal_of_small_discriminant`,
`isMinimal_of_small_c4`, `isMinimal_of_small_c6`. They apply over a general DVR
with fraction field, an integral curve, and an integer-valued valuation whose
integer ring is that DVR. The thresholds are `exp(-12)`, `exp(-4)`, `exp(-6)`.
They conclude Mathlib's `IsMinimal`; no new minimal-model definition is involved.

Target: TauCeti `MinimalModel/Basic.lean` or an adjacent criteria file. Preserve
valuation direction and normalization. Acceptance: compile without project
imports or assumptions, retain a private discrete-value-group helper, and
replace the downstream arithmetic imports. Search newer upstream revisions for
equivalent lemmas before opening a PR.

## TC-02 — extracted special criterion at two

Status: proved source, extracted into
[`TwoAdicMinimality.lean`](../VerifiedLcalc/UpstreamCandidates/TauCeti/TwoAdicMinimality.lean).

Declarations: `WeierstrassCurve.integral_c4_two_adic_gap` and
`isMinimal_of_two_adic_c4_six`. An integral c4 is a unit or has valuation at most
`exp(-4)`; c4 valuation `exp(-6)` then forces minimality. The explicit hypothesis
is `v(2) = exp(-1)`. This is not a claim covering arbitrary ramification at two.

Target: TauCeti `MinimalModel/`. Acceptance: retain the stated hypotheses,
standard-only axiom audit, and the small rational-curve regression exercising
the criterion. Keep the integer divisibility/witness dispatcher in this project.

## TC-03 — extracted computable point counts and transport

Status: proved source in
[`PointCount.lean`](../VerifiedLcalc/UpstreamCandidates/TauCeti/PointCount.lean).

Declarations: `WeierstrassCurve.pointCountFinite`,
`pointCountFinite_eq_pointCount`, `pointCount_map_equiv`, and
`frobeniusTrace_map_equiv`. The finite API takes `Fintype` and decidable equality;
the mathematical arbitrary-field count keeps its existing `Nat.card` definition.
Both include singular affine solutions. No ellipticity assumption should be
added to the projective-model count.

Target: TauCeti `PointCount.lean`. Acceptance: replace the pinned-port import
with the upstream import, check characteristic-two/three singular examples,
and compare kernel evaluation with the integer-modulo enumerator before
replacing that implementation. The general equality proof is not a performance
measurement.

## TC-04 — reuse existing global minimality; prove the completion bridge

Status: canonical predicate already exists; comparison theorem is not proved
here. Reuse TauCeti's `WeierstrassCurve.IsGlobalMinimal` and its introduction,
elimination and `isGlobalMinimal_iff` API in `GlobalMinimalModel.lean`.

Required theorem: minimality over the localization of a Dedekind domain at a
height-one prime is equivalent to minimality after base change to its adic
completion, with the corresponding valuation integer ring. State the exact
algebra maps, integrality and ellipticity hypotheses against the selected pin.
The forward/reverse directions must not be assumed definitionally equal.

Prerequisites: TauCeti localization/fraction-field instances, normalized
valuation comparison, transport of integral equations/changes, and the required
completion descent or approximation argument. Acceptance: a generic theorem,
standard-only axioms, then a proved rational specialization replacing the local
`GloballyMinimalInput` completion predicate. No new axiom is an acceptable bridge.

## TC-05 — interpret the wild-prime support guard through existing reduction APIs

Status: TauCeti's `IsSemistable` and no-additive-reduction equivalences exist in
`MinimalModel/Semistable.lean`. Our `tameAtWild` checks only primes 2 and 3;
it is not global semistability and permits additive reduction at larger primes.

Required theorem: under the appropriate minimal-model identification, that
Boolean is true exactly when the curve has good or multiplicative reduction at
both rational primes 2 and 3. Reuse the existing local reduction definitions and
semistability lemmas; keep the executable guard and its limited scope explicit.
TC-04 is the integration prerequisite when switching to localization APIs.

## TC-06 — intrinsic conductor and tame formula

Status: missing geometric/representation-theoretic bridge. No matching elliptic
Artin-conductor API was found in the checked TauCeti source. Existing conductors
for ideals, ray-class characters and Hecke characters are different objects.

Required results: identify conductor exponents as zero at good reduction, one
at multiplicative reduction, and two at additive primes of residue characteristic
at least five. Prove the global norm/product formula; specialize to Q and show
that the guarded executable `tameLevel` computes it. Bad-prime formulas must use
minimal models. Then remove the corresponding assumed compatibility fields.

Acceptance: use an agreed intrinsic conductor (Neron model or etale/Galois
representation), prove local/global normalization, and audit arithmetic
independently of modularity. Integer-case classification alone is insufficient.

## TC-07 — local epsilon factors and root-number formulas

Status: missing analytic/representation-theoretic interpretation. The current
code verifies arithmetic formulas and tables, while their epsilon-factor
compatibility remains explicitly assumed.

Required results: good/multiplicative/tame additive local signs, the wild formulas
at two and three, the real-place convention, and the global product. Fix additive
character and measure conventions and prove the normalized result independent
of auxiliary choices. This needs epsilon-factor infrastructure, not just TC-06.
Preserve the GPL provenance of the existing wild tables; review licensing before
moving their implementation into an Apache project.

## Submission and validation

The first three entries have compiled source rather than proposed axioms. The
remaining entries are proof obligations. Run `make test-lean` and
`tests/UpstreamCandidates.lean` against the agreed pin, inspect axiom dependencies,
then replace local imports with the accepted upstream APIs. Modular realizations,
checked derivative enclosures and certification remain separate from these local
arithmetic results. The broader extraction roadmap is
[ELLIPTIC_LOCAL_ARITHMETIC.md](roadmaps/ELLIPTIC_LOCAL_ARITHMETIC.md).
