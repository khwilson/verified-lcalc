# Elliptic arithmetic: extraction and missing geometric bridges

Companion to [the audit and version matrix](../TAUCETI_ROADMAP.md). Statements below are interface proposals. Existing signatures quoted from this repository are real source declarations; suggested new geometric interfaces are specifications, not compiled declarations or new axioms.

## M1: arithmetic Euler-product extraction (Mathlib)

[Current proof](../../VerifiedLcalc/EllipticCurve/EulerProduct.lean), namespace `VerifiedLcalc.EulerProduct`, proves `ofPowerSeries_apply_of_coprime`, `mul_apply_congr_right`, `prod_apply_eq_one_on_divisors`, then this result:

```lean
-- Existing local signature; open ArithmeticFunction.
theorem apply_prime_pow {ι R : Type*} [CommRing R]
    (q : ι → ℕ) [Northcott q] (f : ι → PowerSeries R)
    (hf : ∀ i, (f i).constantCoeff = 1) (i₀ : ι) (hp : (q i₀).Prime)
    (hc : ∀ i, i ≠ i₀ → (q i).Coprime (q i₀)) (k : ℕ) :
    eulerProduct (fun i => ofPowerSeries (q i) (f i)) (q i₀ ^ k) =
      PowerSeries.coeff k (f i₀)
```

Target `Mathlib/NumberTheory/ArithmeticFunction/LFunction.lean` or a small adjacent file. This concerns stabilization of arithmetic coefficients, not convergence of a complex Euler product. Retain explicit constant-term and coprimality hypotheses. First search for a newer generalized coefficient theorem. Acceptance: abstract coefficients/bases, including `k = 0`; no EC imports; downstream `GlobalCoefficients.lean` uses the result unchanged.

## M2: DVR minimality (TauCeti, eventually Mathlib)

Relevant local files: [LocalModel](../../VerifiedLcalc/UpstreamCandidates/TauCeti/LocalModel.lean), [AdditiveArithmetic](../../VerifiedLcalc/EllipticCurve/Tate/AdditiveArithmetic.lean), [InvariantMinimality](../../VerifiedLcalc/EllipticCurve/Tate/InvariantMinimality.lean), [TwoAdicMinimality](../../VerifiedLcalc/EllipticCurve/Tate/TwoAdicMinimality.lean).

The reusable scope is `WeierstrassCurve K`, a DVR `R`, fraction field `K`, and an integral-model hypothesis. For example this is the existing c4 criterion:

```lean
variable {R K : Type*} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem isMinimal_of_small_c4 (W : WeierstrassCurve K)
    [WeierstrassCurve.IsIntegral R W]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : v.Integers R)
    (hc : WithZero.exp (-4 : ℤ) < v W.c₄) :
    WeierstrassCurve.IsMinimal R W
```

The c6 version has exponent `-6`; the discriminant version `-12`. Multiplicative valuations reverse the familiar additive-valuation intuition: preserve the actual inequality instead of translating informally. Also extract `isMinimal_of_unit_discriminant`, `isMinimal_of_unit_invariants`, `integralModel_eq_of_baseChange`, and reduction under integral variable changes where upstream does not already cover them. The residue-characteristic-two c4 gap needs its own hypotheses and proof; the executable Q divisibility adapter stays here.

Target existing `TauCeti/AlgebraicGeometry/EllipticCurve/MinimalModel/` files. Acceptance: work over a general DVR; reuse the existing minimality definition; distinguish arbitrary integral equations from minimal ones; prove invariance of any resulting local factor under permitted model changes. No new bundled elliptic-curve representation and no certificate records in these statements.

## M3–M5: reduction, coefficients and explicit growth

At the pinned TauCeti revision, `PointCount.lean`, `SingularPointCount.lean`, `LocalPolynomial.lean` and the `MinimalModel/` directory already supply the foundations. [Local adapters](../../VerifiedLcalc/EllipticCurve/TauCeti.lean) include `pointCount_map_equiv`, `frobeniusTrace_map_equiv`, `localPolynomial_eq_computed`, and `localPowerSeries_coeff_eq`. General field-equivalence invariance belongs upstream; integer-array encoding of an input equation does not.

[GlobalCoefficients](../../VerifiedLcalc/EllipticCurve/GlobalCoefficients.lean) proves:

```lean
-- Existing Q-specific statement; namespace/open declarations omitted.
theorem LFunction_apply_prime_pow (W : WeierstrassCurve ℚ)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    W.LFunction (p ^ k) = PowerSeries.coeff k
      ((W.baseChange ((rationalPlace p).adicCompletion ℚ)).localPowerSeries
        ((rationalPlace p).adicCompletionIntegers ℚ))
```

Its prerequisites are `completion_residue_card`, `rationalPlace_norm`, and `LFunction_apply_norm_pow`; see [RationalPrimes](../../VerifiedLcalc/EllipticCurve/RationalPrimes.lean). The norm-injectivity argument is specific to Q. Over a general number field, different primes can have equal norms and several local factors contribute to a rational-prime coefficient. A correct generalization groups all places over the prime and accounts for residue degrees; it cannot simply replace Q by K in the displayed theorem.

[GlobalBounds](../../VerifiedLcalc/EllipticCurve/GlobalBounds.lean) proves `bad_reduction_trace_abs_le_one`, `LFunction_primePower_recurrence`, and:

```lean
theorem LFunction_abs_le_cube (W : WeierstrassCurve ℚ) (n : ℕ) :
    |W.LFunction n| ≤ (n : ℤ) ^ 3
```

This bound is deliberately weak and explicit, and is independent of modularity. A stronger Hasse bound is not a missing theorem to reinvent. Use existing trace estimates where available; extract the recurrence-to-growth lemma separately if useful beyond ECs. Acceptance: include good, multiplicative and additive places, explain the convention at index zero, and establish the bound for the abstract L-function rather than just a checked finite prefix. M4/M5 should target the EC L-function namespace once the selected newer multiplicativity source is integrated against a consistent dependency graph.

## T1: Tate reduction transcript is an algorithmic theorem

The pinned TauCeti release provides `IsTateTerminal` for each algorithmic
symbol and `reductionSymbol_eq_of_isTateTerminal` to compare a terminal equation
with the canonical local symbol. The project checks a supplied integral
translation by evaluating the same terminal predicate over ℤ and then
transports the result to the local ring. This certifies exact additive symbols
when the input contains the translation. The formal Tate q-curve and its
specialization are a separate strand of the roadmap.
[Stopping conditions](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/TateAlgorithm/Terminal.lean#L105-L139)
· [Canonical symbol comparison](https://github.com/TauCetiProject/TauCeti/blob/e0e414ce57522ba17560057ad0d7f2edab91bf0c/TauCeti/AlgebraicGeometry/EllipticCurve/TateAlgorithm/Reduction/Curve.lean#L117-L137).

Current local sources [WildTateCore](../../VerifiedLcalc/EllipticCurve/Tate/WildTateCore.lean) and [WildArithmetic](../../VerifiedLcalc/EllipticCurve/Tate/WildArithmetic.lean) check transformations, divisibility, polynomial conditions and wild paths. `tateWitness_valid_correct` equates `TateWitness.Valid` with an `ArithmeticSpec` involving additive reduction, a path, and a discriminant-valuation bound. It does **not** identify a geometric fiber, Artin conductor or local epsilon factor. Search soundness (`tateWitness?_sound`, `wildData?_sound`) is distinct from algorithm completeness.

Proposed upstream output:

- A typed algorithmic reduction symbol, with the integer discriminant valuation, component-count formula, residue-polynomial splitting data, and the transformation transcript.
- A validity predicate stated using `WeierstrassCurve`, valuation-ring data and residue fields. Use the existing `WeierstrassCurve` type, with no Q-only finite record in the mathematical specification.
- Separate theorems for a valid transcript's arithmetic meaning, mutually exclusive branches, independence from valid transformation choices, existence of an output, and termination of a specific search implementation.

The existing [elliptic roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/EllipticCurves/README.md) already distinguishes an algorithmic `ReductionSymbol` and Ogg expression from geometric conductor theory. Align names and scope with that design. Its algorithmic and analytic Tate-curve strands should remain distinct. For residue 2 and 3, state the precise characteristic and completeness assumptions rather than extrapolating the tame proof.

Acceptance: an independently stated mathematical specification for every branch, parameterized positive-characteristic residue fields where possible; table transcription alone is insufficient. Initially the theorem can stop at the algorithmic symbol and exponent. That milestone must not be advertised as discharging `wildLevel_eq`.

## T2/T3: the geometric statements needed to remove arithmetic assumptions

These require genuine new mathematical objects. Proposed *statement shapes*, deliberately not Lean declarations until their carrier APIs exist:

1. For an elliptic curve over a local field, a prime ℓ different from the residue characteristic, and its ℓ-adic Tate-module representation: `artinConductorExponent representation = algorithmicOggExponent transcript`, for a valid transcript of a minimal equation. Define inertia action, Swan contribution, finite conductor and normalization before stating this identity. In the wild cases a tame-only argument is inadequate.
2. For that local representation with fixed additive character and measure normalization: `localEpsilonSign representation character = computedLocalRoot transcript`. State and prove independence of auxiliary choices in the normalized root number. Character conventions at 2, 3 and the archimedean place affect the global product.
3. For E/Q: the global arithmetic conductor is the product of prime powers from these exponents, and the global root is the product of local signs. Then prove the normalized modular realization has that level and sign. Distinguish the minimal newform level from an arbitrary higher-level realization of the same L-series.

The current assumption fields [wildLevel_eq / wildSign_eq](../../VerifiedLcalc/EllipticCurve/Modularity/ArithmeticRealization.lean) shortcut all these layers. The algorithmic lemmas `wildExponent_correct` and `wildLocalRoot_correct` identify code with arithmetic formulas, while the similarly named fast-path equalities identify two computational definitions. None supplies the representation-theoretic identities above.

Coordinate T2 with the existing Néron-model/conductor workstream; do not build an incompatible geometric model just to close a record field. T3 deserves its own roadmap/owner because epsilon-factor normalization is not a corollary of transcript correctness. Full normalized modularity remains an additional global theorem even after T2/T3.

## Licensing and PR review gates

The selected TauCeti ports retain their Apache attribution; consult [PROVENANCE.json](../../VerifiedLcalc/Upstream/TauCeti/PROVENANCE.json) before upstreaming. The wild-root implementation has PARI provenance and a [GPL notice](../../LICENSES/PARI-GPL-2.0-or-later.txt). Review compatibility before moving implementation or tables into an Apache project; use an appropriately licensed contribution or independently justified compatible implementation. Mathematical truth and permission to copy source are separate questions.

For each PR: identify the original declaration and target file; compile against the agreed pin; audit for sorry/custom axioms; replace the corresponding local adapter and check downstream theorem/axiom equivalence. Existing finite witnesses are regression inputs, not the proof of universal algorithm correctness. No full build was performed for this document-only audit.


## Computable finite-field counts

A local upstream candidate, `WeierstrassCurve.pointCountFinite`, now enumerates
solutions using `[Fintype F] [DecidableEq F]` and proves equality with TauCeti's
existing `pointCount`. See [the API and migration notes](../COMPUTABLE_POINT_COUNTS.md).
The certificate backend now uses the shared finite-ring evaluator and its
generic bounds directly. Retain the arbitrary-field mathematical specification
and measure kernel performance independently of the correctness proofs.

## Existing global-minimality API and completion bridge

The full pinned TauCeti checkout also contains
`TauCeti/AlgebraicGeometry/EllipticCurve/GlobalMinimalModel.lean`:
`WeierstrassCurve.IsGlobalMinimal O W` means Mathlib minimality over
`Localization.AtPrime v.asIdeal` for every height-one prime `v`. Its public
interface includes `isGlobalMinimal_iff`, `IsGlobalMinimal.isMinimal`, and
`IsGlobalMinimal.of_forall_isMinimal`. This definition already exists and must
not be reinvented. The file additionally proves global integrality and
integral-change-of-variable results, and points to LeanBridge provenance.

The canonical interface is now ported, and the custom `GloballyMinimalInput`
definition is removed. `EllipticCurve/GlobalMinimality.lean` proves the finite
witness criteria directly in these localizations, using TauCeti's valuation
integer-ring identification. A witness supplies canonical global minimality
for the conductor/sign assumptions, and independently supplies completion
minimality for Mathlib's numerical Euler-factor path.

The full localization/completion equivalence remains a useful general theorem,
but is not required for this integration strategy. Neither direction is
assumed by the new witness proof. Completion minimality should descend through
integral variable changes and valuation comparison; preservation towards the
completion additionally requires the appropriate base-change argument. This
remaining general comparison is tracked as TC-04.
