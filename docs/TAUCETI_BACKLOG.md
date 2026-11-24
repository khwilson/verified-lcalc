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


## TC-15 — finite certificates for complete rational isogeny classes

`certify_ec` accepts distinct and exhaustive representatives with proofs of
attainment and minimality for every ordered pair. To construct that evidence
from finite data, prove that minimum-degree isogenies have cyclic kernels
by removing a multiplication factor when the kernel is noncyclic. Then prove
that the cyclic isogenies decompose into rational prime-degree steps. At each
vertex, certify that all rational prime-degree quotients are represented, using a
proved bound on the possible primes and exhaustion of Galois-stable cyclic
kernels. Then prove lower bounds on all isogeny degrees between each pair
from the finite evidence, including composite degrees. The fixture for
37.a1 explicitly takes the single representative's exhaustivity as a premise.

At the pinned TauCeti revision the verifier uses
`Isogeny.degree_comp`, `Isogeny.degree_variableChangeIsogeny`, and
`WeierstrassCurve.IsReducedMinimal`. It uses the pinned Mathlib
`Finset.max'_mem` and `Finset.le_max'` to derive the maximum.
[TauCeti change of variables](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/VariableChange.lean)
· [TauCeti reduced minimal models](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/Reduced.lean)
· [Mathlib finite set maximum](https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/Data/Finset/Max.lean)

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

## TC-17 — geometric CM and minimum-conductor quadratic twists

Status: geometric endomorphism ring and minimum-conductor witnesses are accepted
by the certificate verifier. The proof of the conductor lower bound from the
denominator of j is in
[`ConductorDenominator.lean`](../VerifiedLcalc/UpstreamCandidates/TauCeti/ConductorDenominator.lean).
The reduced equation of 37.a1 attains this bound across its quadratic twists.

Target: TauCeti `Isogeny/Hom/ComplexMultiplication.lean` for the geometric
endomorphism classification over the separable closure of ℚ. A classifier
should prove that the full ring is ℤ or a specified order, including the
exhaustivity of possible endomorphisms.

Target: TauCeti `QuadraticTwist/` and
`TateAlgorithm/Reduction/Conductor.lean` for an exhaustive finite candidate
reduction over ℚ. Prove that at least one candidate attains the global
minimum and describe equal-conductor candidates. The catalogue's choice
among tied or exceptional candidates needs its own comparison. The denominator
lemma reuses `exists_smul_eq_reducedMinimalModel`, `variableChange_j`,
`algorithmicConductor_smul`, and
`IsGlobalMinimal.dvd_absNorm_algorithmicConductor_iff`.
[Pinned reduced-model API](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/Reduced.lean) · [Pinned conductor API](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/TateAlgorithm/Reduction/Conductor.lean)

The modified Szpiro checker uses Mathlib's `lowerLog_spec` and the exact
algorithmic conductor norm, with global minimality and the norm identification
supplied as proofs. A useful future bridge would derive the latter from a
checked finite Tate transcript without invoking modularity.
[Pinned directed logarithm](https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Log.lean)

## TC-18 — complete local images and certified torsion-field actions

Target G1 in the [EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md).
For a nonsingular elliptic curve over ℚ with `HasGeometricCM`, prove that its
rational j-invariant is integral. For geometrically non-CM curves over ℚ, prove
effective exhaustion of exceptional primes under explicit arithmetic hypotheses.
Combine this with lifting criteria from finite reductions to the full Tate
module, with separate depth hypotheses at 2 and 3.

For a given positive modulus, use an ordered basis of all geometric torsion.
Prove that whenever a splitting field is generated by the coordinates of that
basis, its Galois action induces precisely the same subgroup of the basis
matrices as the absolute Galois action. An exact finite generator computation
can then use completeness of the splitting-field automorphism action.

The pinned APIs are `HasGeometricCM`, `torsionGaloisAction`,
`nonempty_basis_torsionBy`, and `tateModuleGaloisRepresentation`. A separate
adelic comparison needs compatible torsion bases and the congruence-kernel
containment theorem for the resulting adelic image.
[Pinned finite action](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Galois.lean)
· [Pinned Tate-module action](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/TateModule/Galois.lean)
· [Candidate profinite API](https://github.com/TauCetiProject/TauCeti/pull/45304)

## TC-19 — explicit canonical-height error over ℚ

The certificate command checks a supplied enclosure against
`WeierstrassCurve.Affine.Point.canonicalHeight` in the logarithmic
x-coordinate normalization. The 37.a1 fixture proves one such enclosure
using an upper bound for the doubling map and exact evaluation at 8P.

The reusable target is an explicit, computable nonnegative bound depending
on an integral nonsingular Weierstrass equation over ℚ for
`|P.canonicalHeight - P.naiveHeight|`, uniform in the rational point P.
The pinned TauCeti result `Point.abs_canonicalHeight_sub_naiveHeight_le`
provides an existential constant. Combine upper and lower height estimates
for the projective duplication map on the given equation with the
canonical-height doubling law. An explicit uniform bound then gives an
error divided by `4^n` when enclosing the height using the naive height of
`2^n • P`. Include points at infinity, torsion, and nonminimal equations
in the specification unless a particular bound explicitly assumes minimality.

## TC-20 — complex period area and Faltings ratio

The certificate uses TauCeti's `WeierstrassCurve.periodLattice` and Mathlib's
`ZLattice.covolume` to state the Euclidean period area. The input model and
every representative used for the class ratio are globally minimal. The
stable height uses an explicit formula in terms of area, discriminant and
the rational j-invariant denominator.

For a nonsingular rational Weierstrass equation, relate the complex covolume
of the normalized period lattice to period integrals or other computable
analytic data, with explicit rational error bounds. Include both signs of
the discriminant and specify the invariant differential and real-component
normalization. For the stable height, compare the logarithmic correction
with the change of minimal discriminant under semistable base change. For
the class ratio, relate pullback of Néron differentials along rational
isogenies to maps of period lattices and prove the hypotheses under which
the maximum-to-input area ratio is an exact lattice index. Those results
would let callers construct witnesses without independently supplying area
enclosures and exact class comparisons.

[Pinned period lattice](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/Analysis/SpecialFunctions/Elliptic/Period/Lattice.lean)
· [Pinned covolume](https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/Algebra/Module/ZLattice/Covolume.lean)

An upstream review at TauCeti `fb3fbc9f05780f456267a29168dfae7a98c2d8d0`
found the normalized lattice and real-period APIs. The related open PR
#43196 develops the real-period isogeny formula with Tamagawa and Kummer
ratios. The complex maximum-to-input lattice index remains a separate target.
[Reviewed pull request](https://github.com/TauCetiProject/TauCeti/pull/43196)

## TC-21 — normalized p-adic heights and regulators over ℚ

- **Roadmap target:** [LMFDB G3](roadmaps/LMFDB_Q_CERTIFICATION.md#g3--iwasawa-invariants-and-p-adic-regulator).
  Define the normalized ordinary cyclotomic p-adic height pairing of a rational
  elliptic curve at a good ordinary prime, with the differential and
  logarithm normalization explicit. Prove descent modulo torsion, bilinearity
  and symmetry. Define the regulator as the height matrix determinant on a
  basis of the free Mordell–Weil quotient and prove independence of that
  integral basis. Supply a checked evaluator for the pairing and determinant
  with an absolute-precision error bound, including negative valuations.
- **Source comparison:** Identify the normalization and the specific curve used
  for the stored class row. A proposed class-to-curve transfer also needs the
  relevant change-of-model or isogeny theorem, with its scaling factor.
  [LMFDB renderer](https://github.com/LMFDB/lmfdb/blob/a0c7fdc3b7ab1d7f11d324242e4707896c5b3529/lmfdb/elliptic_curves/elliptic_curve.py#L775-L792)
- **Existing interfaces:** TauCeti `e0e414ce` provides Mordell–Weil finite
  generation and the ordinary trace criterion
  `WeierstrassCurve.isOrdinary_iff_not_dvd_frobeniusTrace`. Mathlib `31ce06ea`
  provides `Padic` and `Matrix.det_isEmpty`. At rank zero the determinant is
  already checked on the actual empty Mordell–Weil index set.
- **Proof-parametric stored-row support:** `IsWeierstrassParameterSeries`,
  `weierstrassParameterDeriv`, and `IsNormalizedOrdinarySigma` state the
  model-specific Laurent differential characterization with integral
  coefficients, leading term, and parity under formal negation.
  `ordinaryPadicHeightAtMultiple` fixes the logarithm and denominator
  conventions. `StoredPadicRegulatorEvidence` retains the hypotheses
  determining the class model, the rank-one basis lift, the exact multiple
  with nonsingular reduction at finite places, and the independent sigma
  argument approximation. The finite logarithm comparison is proved
  from that approximation. Formal existence and uniqueness, change of model,
  and an independently certified ordinary sigma implementation remain
  mathematical prerequisites for closed evidence.
  [Blakestad–Grant, Theorem 8 and Remark 11](https://arxiv.org/abs/1903.02480)
  · [Sage ordinary height procedure](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/schemes/elliptic_curves/padics.py#L658-L860)

## TC-22 — certified residual conjugacy classes and completeness

Target G1 in the [EC/Q coverage roadmap](roadmaps/LMFDB_Q_CERTIFICATION.md).
For a nonsingular elliptic curve over ℚ and a prime ℓ, identify the absolute
Galois image on all geometric ℓ-torsion with the matrices of the splitting
field action on an ordered torsion basis. Prove that change of basis gives
conjugate subgroups and derive a finite check from a certified description
of the splitting field. For geometrically non-CM curves over ℚ, pair a
checked residual image at each candidate exceptional prime with explicit
arithmetic hypotheses ensuring surjectivity at all other primes. For
geometrically CM curves, determine the appropriate comparison subgroup and
prove the hypothesis under which the representation attains it.

The project reuses `WeierstrassCurve.torsionGaloisAction`,
`WeierstrassCurve.nonempty_basis_torsionBy`, `Matrix.GeneralLinearGroup`,
`Subgroup.closure`, `Subgroup.map`, and `MulAut.conj`. The catalogue label
semantics use the representative matrices from Sutherland's Section 6.4
and Table 3. The checked interface requires explicit image and conjugacy
proofs, so neither the catalogue nor a conjecturally complete label
classification supplies a geometric premise.
[Pinned finite action](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Galois.lean)
· [Pinned torsion basis](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Torsion/Structure.lean)
· [Pinned inner automorphisms](https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/Algebra/Group/End.lean)
· [Candidate open-subgroup API](https://github.com/TauCetiProject/TauCeti/pull/45304)

## TC-23 — certified conductor rosters and catalogue ordering

- **Roadmap target:** [LMFDB I1](roadmaps/LMFDB_Q_CERTIFICATION.md), with a
  second completeness problem for all rational isogeny classes at a fixed
  conductor. A supplied `ConductorClassRoster` proves that the subject and each
  representative have the same actual algorithmic conductor norm. Its
  exhaustivity theorem covers arbitrary nonsingular rational equations with that
  conductor. Strict first-difference order uses their arithmetic `LFunction`
  coefficients. Isogeny invariance implies the listed classes are distinct.
- **Missing constructor:** Produce that roster from certified enumeration and
  exclusion, using hypotheses for the stated conductor range and an effective
  bound or witness for the first differing normalized arithmetic coefficient of
  each pair. The within-class ordered reduced minimal model constructor remains
  part of TC-15. No computed label or hash supplies either exhaustivity claim.
- **Existing interfaces:** TauCeti `e0e414ce` supplies `algorithmicConductor`,
  `Isogeny.LFunction_eq`, `LFunction`, and reduced minimal models. Mathlib
  `31ce06ea` supplies `Nat.digits` and `Nat.ofDigits_digits`.
  [LMFDB label convention](https://www.lmfdb.org/knowledge/show/ec.q.lmfdb_label)
  · [Sage base-26 producer](https://github.com/sagemath/sage/blob/develop/src/sage/databases/cremona.py#L168-L236)

## TC-24 — exact adelic images and modular-curve signatures

Target [LMFDB G1](roadmaps/LMFDB_Q_CERTIFICATION.md). For a nonsingular
elliptic curve over ℚ, give a compatible family of Tate-module bases and
compare the image of one absolute Galois action with the full inverse image
of a certified finite matrix subgroup. Prove sufficient hypotheses for
full congruence-kernel containment, including entanglement across primes,
and prove a finite test for minimality of the modulus.

For an open subgroup of the integral adelic `GL₂`, pull back its reduction
to `SL₂(ℤ)` and take the effective image in `PSL₂(ℝ)`. For the resulting
compactified quotient, derive finite CW type and an Euler-characteristic
formula in terms of the index, elliptic stabilizers and cusps. Identify
elliptic points with fixed points of the standard order-two and order-three
actions on projective cosets and identify cusps with translation orbits.
These bridges would let a finite orbit certificate derive the topological
genus. Separately, formalize comparison with the catalogue conjugacy-class
identifier when a complete suffix is supplied.

The pinned interfaces are TauCeti's `tateModuleGaloisRepresentation`,
`Subgroup.CompactifiedQuotient`, `FiniteCWType`, and
`RiemannSurface.genus_eq_of_eulerChar_eq`, with Mathlib's `ZMod.equivPi`,
`Matrix.GeneralLinearGroup.piEquiv`, and `Subgroup.index_map_eq`.
[Candidate adelic group and level API](https://github.com/TauCetiProject/TauCeti/pull/45304)
· [Pinned compactification](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/Analysis/Complex/Fuchsian/Compactification/Basic.lean)
· [Pinned genus API](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Genus.lean)

## TC-25 — Faltings order and intrinsic torsion

The Faltings index counts exact predecessors in the proved complete ordered
class. For ties in Faltings height, order by native LMFDB number, which is the
lexicographic order of the five coefficients of the reduced minimal equations.
To derive witnesses, supply certified comparisons of complex areas of
globally minimal isogenous equations, including exact equality when areas tie.
Strict rational enclosures can separate distinct heights, while the tie case
needs an exact area comparison.
[Catalogue sort rule](https://github.com/JohnCremona/ecdata/blob/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/scripts/files.py#L739-L767)

The intrinsic torsion checker proves order one from trivial full rational
torsion. For general elliptic curves over ℚ, define the symmetric pairing on
rational torsion with values in ℚˣ ⊗ ℚ/ℤ from functions with divisor
`n(P) − n(O)` evaluated by residue-field norms on disjoint degree-zero
divisors representing `Q − O`. Prove choice independence and biadditivity.
For a proved finite rational torsion presentation, evaluate the pairing on
its generators, then compute the exact kernel and its cardinality. A useful
test has nontrivial rational torsion and a proper radical. The pinned TauCeti
revision supplies the divisor and Weil pairing infrastructure, including
`Isogeny/DivisorPullback.lean`. The target pairing uses rational divisors
and a tensor-valued evaluation.
[LMFDB definition](https://www.lmfdb.org/knowledge/show/ec.intrinsic_torsion)
· [Yamazaki, Yang, Yoo and Yu](https://arxiv.org/abs/2512.00787v3)

## TC-26 — complete trace fingerprint inputs

- **Roadmap target:** [LMFDB rational trace fingerprint](roadmaps/LMFDB_Q_CERTIFICATION.md).
  The current checker accepts an exact vector of all prime coefficients at
  primes in `[4096,8192)`. The arithmetic object is the prescribed weighted
  sum modulo `2^61 - 1`. The input proof must identify each coefficient,
  including any bad prime in the interval, with the curve's `LFunction`.
- **Missing constructor:** Build the full vector efficiently from a nonsingular
  rational equation and exact reduction evidence. Reuse proved finite-field
  point counts for good primes and checked local minimality and reduction
  for bad primes. Any batch acceleration needs a correctness theorem against
  the arithmetic `LFunction` values.
- **Existing interfaces:** TauCeti `e0e414ce` supplies `LFunction` and
  `Isogeny.LFunction_eq`. Mathlib `31ce06ea` supplies integer remainders and
  the decidable prime predicate. The existing `primeCoefficientsValid_sound`
  theorem can justify individual entries when its finite checks succeed.
  [LMFDB producer and weights](https://github.com/LMFDB/lmfdb/blob/28f9f0e38f2f027b13edcb2facece1bb45b47170/lmfdb/utils/trace_hash.py)

## TC-27 — historical Cremona ordering

- **Roadmap target:** [LMFDB I1](roadmaps/LMFDB_Q_CERTIFICATION.md).
  A complete isogeny-class or curve ordering at a supported conductor defines
  the historical isogeny and isomorphism indices. The singleton cases
  require only the corresponding exhaustivity from TC-15 and TC-23,
  together with the actual algorithmic conductor norm from 1 through 500000.
- **Missing comparison:** For larger indexing sets, connect each historical
  index to that of an independently authenticated, versioned published
  catalogue, or reproduce the historical algorithm and prove its order.
  Include the documented special choice of optimal curve in the 990h
  class. The LMFDB lexicographic order cannot supply the historical indices
  in general.
- **Existing interfaces:** Reuse the pinned TauCeti `algorithmicConductor`
  and rational isogeny definitions at `e0e414ce`, together with the
  project's complete isogeny class and conductor roster proofs.
  [LMFDB convention](https://www.lmfdb.org/knowledge/show/ec.q.cremona_label)
  · [Pinned Cremona tables](https://github.com/JohnCremona/ecdata/tree/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allcurves)
  · [Sage historical index conventions](https://github.com/sagemath/sage/blob/10.5/src/sage/databases/cremona.py)

## Reusable declarations from the certificate and performance audit

The pinned review used Mathlib `31ce06ea` and TauCeti `e0e414ce`. The upstream
search inspected Mathlib `e62b985f`, TauCeti `284d4551`, and open pull requests
for dyadic interval evaluation, Horner arithmetic, and integral adelic
images. These are targets for human upstream planning.

- **Mathlib inclusion arithmetic.** The local
  `VerifiedLcalc.Numerics.dyadicPolynomialBounds` and
  `VerifiedLcalc.Numerics.dyadicPolynomialBounds_toRat` compute Horner bounds
  for integer coefficients on a fixed dyadic grid. For equality with the
  rational recurrence, the lower argument endpoint must be nonnegative.
  To derive polynomial soundness, require a real evaluation point between
  the two endpoints and round outward at every step. The local
  `VerifiedLcalc.Numerics.rationalExpDyadicBounds` and
  `VerifiedLcalc.Numerics.rationalExpBounds_correct` are the corresponding
  rational-argument adapter for exponential enclosures. The latter requires
  the real argument to lie between the rational endpoints. The project
  specializes these operations to real Fourier quadrature. The low-level
  exponential evaluator retains David Ledvinka's attribution.
  [Pinned inclusion extensions](https://github.com/leanprover-community/mathlib4/tree/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal)
  · [Related direct dyadic division work](https://github.com/leanprover-community/mathlib4/pull/46315)
- **Mathlib interval division.**
  `VerifiedLcalc.Certification.ratioErrorValid_sound` uses enclosures of
  the real numerator and denominator, a strictly positive lower endpoint
  for the denominator, and a nonnegative rational error radius. It proves
  absolute error about the submitted center by comparing products, which
  avoids a division in the checker. A generic equivalent on an existing
  interval type would serve both the local abc and modified Szpiro checks.
- **Mathlib matrix reduction and TauCeti adelic groups.** The private
  `VerifiedLcalc.padicGL_map_surjective` lifts entries along
  `PadicInt.toZModPow` for a prime and positive exponent, then reflects
  invertibility of the determinant. The matrix lemma generalizes to any
  finite index type and a surjective local homomorphism of commutative
  rings. The local `VerifiedLcalc.adelicCRT`,
  `VerifiedLcalc.adelicReduction` and
  `VerifiedLcalc.adelicReduction_surjective` use positive moduli and combine
  finite matrix lifts with the Chinese remainder decomposition. Coordinate
  these definitions with the upstream integral adelic group and level API.
  [Pinned reduction](https://github.com/leanprover-community/mathlib4/blob/31ce06eaadf4a200c0e1407c5f10953cf606b8f8/Mathlib/NumberTheory/Padics/RingHoms.lean)
  · [TauCeti adelic images PR](https://github.com/TauCetiProject/TauCeti/pull/45304)
- **TauCeti period covolume.**
  `VerifiedLcalc.complexPeriodArea_eq_of_minimal_change` proves area
  invariance for two nonsingular globally minimal rational Weierstrass
  equations related by a rational admissible coordinate change. Factor out
  the general complex area scaling theorem for a nonsingular equation and
  an admissible complex coordinate change, with the square of the norm of
  its scaling factor. The rational minimal-model result then follows from
  the unit scaling factor. This complements the normalized period-lattice
  API. The Faltings height normalizations and catalogue order are local
  adapters.
  [Pinned period lattice](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/Analysis/SpecialFunctions/Elliptic/Period/Lattice.lean)
  · [Pinned complex covolume scaling](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/Algebra/Module/ZLattice/Complex.lean)

The weighted trace fingerprint, LMFDB and Cremona encodings, Faltings
ordering, and partial adelic label formatter describe catalogue conventions
and remain local. The trivial-group specialization
`VerifiedLcalc.IntrinsicTorsionFact.card_radical` uses Mathlib cardinality
directly. The missing reusable result is the rational pairing in TC-25.

## TC-29 — normalized cyclotomic distributions and Iwasawa thresholds

- For weight-two forms on Γ₀(N) with rational coefficients, relate the
  analytic integral in `VerifiedLcalc.Modularity.normalizedRealModularSymbol`
  to TauCeti's integral modular-symbol period map after division by the
  full Néron real period of a globally minimal elliptic curve.
- Prove existence and uniqueness in the integral Iwasawa algebra for
  `OrdinarilyInterpolates` at odd good ordinary primes, and for
  `MultiplicativelyInterpolates` at odd multiplicative primes. Formalize
  the Teichmüller representative and transfer calculations and the
  level-zero identity in `IwasawaLevelZeroIdentity`.
- For good primes at least five with trace zero, construct the signed pair
  and prove `SignedlyInterpolates`, including the level-dependent
  alternating sign of the raw Mazur–Tate element and the two exact
  initial augmentation identities in `IwasawaSignedInitialIdentities`.
  Add the separate cases for p=2 and small supersingular primes.
- `GoodPrimeIwasawaUnitInput.vanishing` derives the ordinary and signed
  conclusions from independent normalized interpolation and augmentation
  data. For the level-eleven fixture, discharge the universal nonanomaly
  and integral-symbol hypotheses using prime-to-p torsion reduction,
  the point-count bounds, and exact normalized modular symbols.
  The exported threshold applies to every good prime in range.
- Pinned TauCeti supplies `cuspIntegral`, `ModularSymbols.periodMap`,
  `WeierstrassCurve.minimalRealPeriod`, and
  `PowerSeries.muInvariant` and `PowerSeries.lambdaInvariant` over a DVR.
  The local verifier reuses these definitions. The native report decoder
  and matched prime selection remain catalogue code. Searched the pinned
  sources and current project for elliptic cyclotomic interpolation. Open
  TauCeti work on the cyclotomic cutoff and growth formula is algebraic,
  and the Coleman norm projector is a different distribution construction.
  [TauCeti PR 42778](https://github.com/TauCetiProject/TauCeti/pull/42778)
  · [TauCeti PR 43208](https://github.com/TauCetiProject/TauCeti/pull/43208)
  · [Pinned DVR invariants](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/RingTheory/PowerSeries/Weierstrass/DiscreteValuationRing.lean)
  · [Pollack, Proposition 6.18](https://math.bu.edu/people/rpollack/Papers/On_the_padic_Lfunction_of_a_modular_form_at_a_ss_prime.pdf)
  · [Pollack–Weston, Mazur–Tate elements](https://math.bu.edu/people/rpollack/Papers/Mazur-Tate_elements_of_modular_forms.pdf)
