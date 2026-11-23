# Prepared TauCeti backlog

The [EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md) records a newer TauCeti source audit and additional proposals for individual LMFDB fields. Use its current declarations when implementing the related adapters.

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

`PointCountOdd.lean` now provides a proved alternative for odd finite fields.
Completing the square identifies each y-fiber with square roots of the quadratic
discriminant; Mathlib's `quadraticChar_card_sqrts` and Euler criterion give its
cardinality. Computation uses Mathlib's binary exponentiation explicitly, so
kernel reduction enumerates only x and performs logarithmically many field
multiplications for the character. The adapter retains the general finite-ring
path for characteristic two and composite moduli. No nonsingularity assumption
is introduced. Include the sign/zero/small-characteristic and axiom regressions
in an upstream proposal.

## TC-04 — canonical global minimality integrated; general comparison remains

Status: the canonical `WeierstrassCurve.IsGlobalMinimal` predicate and its
introduction/elimination interface are now imported from the pinned TauCeti
`GlobalMinimalModel.lean` module. The project-specific `GloballyMinimalInput`
definition is removed. Conductor/sign compatibility uses
`IsGlobalMinimal (𝓞 ℚ) (e.baseChange ℚ)` directly, with the usual ellipticity
instance.

`EllipticCurve/GlobalMinimality.lean` proves every checked minimality criterion
over the localization itself, using TauCeti's fraction-field/DVR instances and
`integers_valuation_of_isLocalizationAtPrime`. Every validated witness therefore
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

## TC-09 — full torsion reduction at odd rational primes

Status: specialization proved in
[`TorsionBound.lean`](../VerifiedLcalc/EllipticCurve/TorsionBound.lean).
Candidate upstream API: for an odd prime `p` and any prime `q`, the integer
`q` lies outside the ideal power `(p)^(q - 1)` in ℤ. Consequently, at
good reduction of an integral rational model at `p`, the order of the entire
rational torsion subgroup divides the cardinality of the reduced point group
over `ZMod p`.

Reuse pinned TauCeti's
[`card_torsion_dvd_card_reduction`](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/TorsionReduction.lean#L269-L282)
and its integral reduction comparison. Keep the executable project-specific
count adapter here. Include `p = 3` and require good reduction of the supplied
equation. The ramification condition excludes the prime `2` from this full
torsion specialization.

## TC-10 — completed Tamagawa factors from rational local data

The pinned release defines `tamagawaNumberAt` on the completed field and
compares it with `tateLocalIndex` on a checked terminal model. Good reduction
and `I₁` both contribute one. For larger multiplicative indices, the terminal
comparison gives `n` in the split case and `gcd(2,n)` in the nonsplit case.
The rational witness adapter still needs to transport its verified splitting
through the residue-field identification and then through the normalized
terminal model. For specific additive factors, connect finite row evidence
to the relevant `IsTateTerminal` and residue-polynomial hypotheses.
[Terminal comparison](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Tamagawa/Local.lean#L144-L162)
· [Split and nonsplit indices](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/TateAlgorithm/LocalIndex.lean#L469-L486)

The A3 certificate uses the product indexed by `HeightOneSpectrum ℤ`,
matching TauCeti's rational BSD quotient. For reuse across local arithmetic
over different presentations of the rational integers, a useful downstream
lemma would transport `tamagawaNumberAt` under a valuation-preserving
`ℚ`-algebra equivalence of completions. Applied to corresponding places of
`ℤ` and `𝓞 ℚ`, this would identify the two finite products and let the
factorization checker reuse already verified local values. The good and
index-one proofs now apply directly to either base ring from the normalized
discriminant and c₄ valuations.

## TC-11 — explicit zero-y Vélu quotient equation

Status: proved locally in
[`DegreeTwoIsogenyRaw.lean`](../VerifiedLcalc/Verification/DegreeTwoIsogenyRaw.lean).
The local `zeroYVelu_eq` calculation identifies TauCeti's general affine
`veluCurve` with the explicit equation below when the rational source is
nonsingular, `a₁ = a₃ = 0`, and `r` is a root of its cubic:

```text
d  = 3 r² + 2 a₂ r + a₄
a₁' = a₃' = 0
a₂' = a₂
a₄' = a₄ - 5 d
a₆' = a₆ - (4 a₂ + 7 r) d
```

Proposed upstream API: `Affine.veluCurve_zero_y`. State it over a field of
characteristic not two with a nonsingular source, `a₁ = a₃ = 0`, and
`r³ + a₂ r² + a₄ r + a₆ = 0`; conclude equality of the general Vélu quotient
and the displayed normalized Weierstrass equation. Keep the kernel explicitly
`{0, (r, 0)}` and prove it has cardinality two from nonsingularity. The
rational adapter additionally requires an elliptic target and an exact change
of target variables.

## TC-12 — minimum degree from distinct j-invariants

Status: proved locally in
[`DegreeTwoIsogeny.lean`](../VerifiedLcalc/Verification/DegreeTwoIsogeny.lean).
For elliptic Weierstrass curves over `ℚ` with unequal j-invariants, every
rational isogeny between their affine models has degree at least two: degree
one implies variable-change isomorphism, which preserves j. Combined with
the witnessed degree-two Vélu isogeny, this proves that two is the attained
minimum in that direction.

Proposed upstream API: `Isogeny.two_le_degree_of_j_ne`. Its hypotheses are
ellipticity of source and target and `source.j ≠ target.j`; its conclusion
applies to each isogeny between their affine models. Keep the field and model
assumptions explicit, and do not claim a lower bound without the j-inequality.

## TC-13 — full rational torsion as two independent cyclic factors

Status: proved in the generic additive-group theorem
[`TwoFactorTorsion.lean`](../VerifiedLcalc/EllipticCurve/TwoFactorTorsion.lean)
and used by `certify_ec` for exact rational two-factor structures. For an
additive commutative group `A`, a point `P` of exact order two, a point `Q` of
positive exact order `n`, `P ∉ AddSubgroup.zmultiples Q`, and
`Nat.card (AddCommGroup.torsion A) ∣ 2 * n`, the theorem constructs an additive
equivalence `ZMod 2 × ZMod n ≃+ AddCommGroup.torsion A` carrying `(1,0)` to `P`
and `(0,1)` to `Q`. The positive order rules out the infinite-cardinality
sentinel; the subgroup-separation hypothesis rules out a dependent order-two
point. TauCeti's full torsion reduction theorem supplies the upper divisor from
two odd good-reduction primes.

Proposed upstream API: a generic Mathlib theorem for this finite abelian group
presentation, separated from the project-specific finite `outsideCyclicCheck`
and elliptic-curve adapter. Preserve the exact-order, nonmembership, positive
order and full-cardinality-divisibility hypotheses. The certificate exports a
concrete additive equivalence rather than only its existence proposition.
Exact torsion prime support is computed with Mathlib's
`Nat.primeFactorsList`; it is emitted only when exact subgroup cardinality is
proved, including the empty support for cardinality one.

TauCeti's open full-two-torsion result (`#44716`) proves a scaled Legendre
normal form from a four-element doubling kernel; it does not give this
generator-preserving equivalence for the full rational torsion subgroup.

## Submission and validation

TC-01, TC-02, TC-03 and TC-08 have compiled source rather than proposed axioms.
The general comparison portion of TC-04 and TC-05 through TC-07 remain proof
obligations. Run `make test-lean` and
`tests/UpstreamCandidates.lean` against the agreed pin, inspect axiom dependencies,
then replace local imports with the accepted upstream APIs. Modular realizations,
checked derivative enclosures and certification remain separate from these local
arithmetic results. The broader extraction roadmap is
[ELLIPTIC_LOCAL_ARITHMETIC.md](roadmaps/ELLIPTIC_LOCAL_ARITHMETIC.md).


## Iterated Mellin derivatives and log moments

[The log-moment theorem](../VerifiedLcalc/Numerics/MellinLogMoments.lean) uses
Mathlib’s `mellin_hasDerivAt_of_isBigO_rpow` and log-weighted decay in an
induction on derivative order. Pinned Mathlib `31ce06e` and TauCeti `e0e414c`
supply the first derivative and the Fricke functional equation. Their generic
log-moment API lacks the arbitrary-order result. TauCeti main’s
`NormalizedContinuation` differentiates the kernel in the integration
variable, which gives a different Mellin identity. Related open results
concern Riemann zeta and Dirichlet L-functions.

The pure log-moment lemma is a candidate for Mathlib’s Mellin transform API.
The cusp-form adapter and its weight-two normalization belong with TauCeti’s
modular L-function interfaces.

## TC-14 — forward analytic-to-Mordell--Weil rank implication in ranks zero and one

Status: temporarily assumed in this project by the separately imported
`Assumptions.LowRankBSD` module. The statement is indexed by one nonsingular
integral Weierstrass equation, an explicit arithmetic modular realization of
that same equation, and a proof that its L-function has exact analytic order
`r` at 1, where `r ≤ 1`; it concludes that the rational point group has
`Module.finrank ℤ = r`. This is the analytic-to-algebraic direction only.

Upstream candidate: a theorem relating the analytic order at the central point
of the normalized modular L-function of an elliptic curve over `ℚ` to the
Mordell--Weil rank in the cases where the exact analytic order is zero or one.
It must state the modularity/normalization identification and all arithmetic
hypotheses explicitly, and reuse the canonical Mordell--Weil rank and
Mathlib/TauCeti L-function definitions. TauCeti's current
`BirchSwinnertonDyer.analyticOrderAt_eq_finrank` already derives the full
rank comparison from its full BSD predicate; this proposal concerns making the
forward low-rank boundary available without importing the leading-coefficient
conjecture. The two converse implications remain
conjectural BSD statements; any future theorem in that direction must list
additional hypotheses (for example suitable Selmer corank and finiteness of
the Tate--Shafarevich group). Search current TauCeti declarations and open
upstream work again before proposing an API; this backlog entry does not claim
the theorem is absent upstream or that the temporary assumption is proved.

## TC-16 — certified full real period evaluation

Pinned TauCeti's `realPeriod_eq_two_mul_pi_div_agm_of_three_real_roots`
and `realPeriod_eq_two_mul_pi_div_agm_of_one_real_root` give exact formulas
once the division polynomial's real roots and their order are established.
For a globally minimal integral model over ℚ, build a computable enclosure
from rational isolating intervals for the nonsingular division polynomial.
Both formulas require verified square-root bounds and a positive AGM
denominator. Repeat the AGM interval updates with rational rounding until
the target radius is proved. The 17.a2 fixture already uses exact roots and
a proved AGM enclosure for its supplied decimal.

[Period formulas](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/Analysis/SpecialFunctions/EllipticIntegral/RealPeriod.lean)
