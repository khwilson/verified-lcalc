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
and retain the finite-ring cardinality/trace bounds. The backend now uses this
shared evaluator, replacing its integer-modulo enumerator. Benchmark kernel
evaluation separately; the equality proof is not a performance measurement.

## TC-04 — canonical global minimality integrated; general comparison remains

Status: the canonical `WeierstrassCurve.IsGlobalMinimal` predicate and its
introduction/elimination interface are now imported from the pinned TauCeti
`GlobalMinimalModel.lean` excerpt. The project-specific `GloballyMinimalInput`
definition is removed. Conductor/sign compatibility uses
`IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ)` directly, with the usual ellipticity
instance.

`EllipticCurve/GlobalMinimality.lean` proves every checked minimality criterion
over the localization itself, using TauCeti's fraction-field/DVR instances and
`integers_valuation_localizationAtPrime`. Every validated witness therefore
proves canonical global minimality at all height-one primes. The existing
completion-minimality theorem separately supplies the numerical coefficient
bridge. Shared finite factorization evidence is proved once. No comparison
between the two minimality predicates is assumed.

Remaining general theorem: minimality over a Dedekind-domain localization is
equivalent to minimality after base change to its adic completion. State the
exact algebra maps, integrality, ellipticity and valuation-normalization
hypotheses. This comparison remains unproved here; its two directions are not
definitionally equal. It is no longer a prerequisite for removing the duplicate
predicate or for the checked-witness conductor/sign path.

Prerequisites for the remaining theorem include transport of integral equations
and changes, valuation comparison, and completion descent/approximation as
needed. Acceptance: a generic proof with standard-only axioms. No new axiom is
an acceptable comparison theorem.

## TC-05 — interpret the wild-prime support guard through existing reduction APIs

Status: TauCeti's `IsSemistable` and no-additive-reduction equivalences exist in
`MinimalModel/Semistable.lean`. Our `tameAtWild` checks only primes 2 and 3;
it is not global semistability and permits additive reduction at larger primes.

Required theorem: under the appropriate minimal-model identification, that
Boolean is true exactly when the curve has good or multiplicative reduction at
both rational primes 2 and 3. Reuse the existing local reduction definitions and
semistability lemmas; keep the executable guard and its limited scope explicit.
Canonical localization minimality is now proved for every checked witness;
the required reduction-model/normalization comparison is still a separate
obligation.

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

## TC-08 — supplied minimal-model bridges

Status: proved source in
[`LocalModel.lean`](../VerifiedLcalc/UpstreamCandidates/TauCeti/LocalModel.lean).

Four generic bridges remain: `isMinimal_of_unit_discriminant`,
`isMinimal_of_unit_invariants`, `reduction_eq_variableChange`, and
`localPolynomial_of_minimal_input`. They reuse the existing comparison,
unit-c4 minimality, variable-change descent and trace-invariance APIs. No exact
complete counterparts were found at the audited pin. The old unit-valuation
wrapper was replaced by Mathlib's `Valuation.Integers.one_of_isUnit'`; the
single-use integral-model equality helper was inlined using existing map APIs.

Target: TauCeti minimal-model/local-polynomial files. Acceptance: preserve the
ambient ring and minimality hypotheses, audit standard axioms, and test supplied
minimal models including singular reductions. These results do not prove the
localization/completion bridge in TC-04.

## Submission and validation

TC-01, TC-02, TC-03 and TC-08 have compiled source rather than proposed axioms.
The general comparison portion of TC-04 and TC-05 through TC-07 remain proof
obligations. Run `make test-lean` and
`tests/UpstreamCandidates.lean` against the agreed pin, inspect axiom dependencies,
then replace local imports with the accepted upstream APIs. Modular realizations,
checked derivative enclosures and certification remain separate from these local
arithmetic results. The broader extraction roadmap is
[ELLIPTIC_LOCAL_ARITHMETIC.md](roadmaps/ELLIPTIC_LOCAL_ARITHMETIC.md).
