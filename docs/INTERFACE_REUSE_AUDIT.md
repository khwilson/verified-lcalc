# Interface reuse audit history

The latest complete per-file review and applied cleanup queue are in
[ELLIPTIC_CURVE_FILE_AUDIT.md](ELLIPTIC_CURVE_FILE_AUDIT.md). The sections below
record earlier findings and follow-ups; their former helper names are historical.

Audit date: 2026-11-19, after cleanup commit `beff8b5c3fcd41fec9e706ba3758c288b08978fa`. This document distinguishes direct API reuse from a mathematical bridge that still needs a proof. It changes no Lean source and reports no new build results.

Sources inspected locally:

- Mathlib `3440367ed1804626334f13a3a534a9cbb3385a59`, checkout `../mathlib4`, with project Lean `v4.36.0-rc2`.
- Full TauCeti `d01c9825761c7e6168457c383458afa8668196a7`, clean checkout `../Igusa/memory/upstream/TauCeti`, using Lean `v4.35.0-rc3`. This is a full-source audit of that pin, not a claim about current remote branches or PRs.
- The project's selected newer TauCeti L-function excerpt at `0642eae29e0a59ef798d04de325386445906e755`; see [provenance](../VerifiedLcalc/Upstream/TauCeti/PROVENANCE.json). The full newer dependency graph has not been integrated by this audit.

The public equation type is now `WeierstrassCurve ℤ`; its map/base change gives the rational curve. Assumptions are isolated in `Assumptions/{Modularity,Precision}.lean`; supplied-realization mathematics lives in `EllipticCurve/Modularity/`, and concrete proof interfaces in `Certification/`. Test fixtures live under `tests/VerifiedLcalcTests/`. The extracted `UpstreamCandidates/TauCeti/{Minimality,TwoAdicMinimality,PointCount}.lean` modules already compile according to the parent build owner; this agent performed source inspection only. See [the upstream backlog](TAUCETI_BACKLOG.md) for implementation sequencing.

## Applied and checked follow-up

After the source audit, the parent applied the direct replacements:

- All `modelC4`/`modelC6` definitions and their tautological adapter lemmas are
  removed. Callers use Mathlib's `c₄` and `c₆` directly.
- `valuationFuel` and `primeExponent` are removed. Callers use kernel-reducible
  `padicValNat`, with `Nat.padicValNat_def` and
  `Nat.multiplicity_eq_factorization` supplying the existing specification.
- `isSquareMod` now reflects Mathlib's finite `IsSquare` decision procedure over
  `ZMod p`, with explicit rejection of modulus zero. Its correctness statement
  covers every nonzero modulus, including composite moduli.

The full Lean build/regression/axiom checks, new upstream-candidate checks,
zero/unit/composite edge tests, Ruff, ty and Python tests passed. No kernel
speedup is claimed without measurement. References to the old loop below
record the audit rationale; those helper definitions are no longer present.
Global-minimality/completion and intrinsic conductor/root-number bridges remain
pending in [the backlog](TAUCETI_BACKLOG.md).

## Audited interfaces and replacement decisions

| Audited helper | Existing API | Recommendation | Proof / performance qualification |
| --- | --- | --- | --- |
| `modelC4`, `modelC6` | `WeierstrassCurve.c₄`, `.c₆` | Replaced by the existing invariant names. | Definitions agree by `rfl`; no new invariant theory is needed. |
| `isPrime` | `decide (Nat.Prime p)` | Already direct reuse; retain a thin Bool adapter where collection code needs Bool. | Mathlib has separate kernel and compiled decision paths. Renaming cannot speed kernel validation. |
| `valuationFuel` / `primeExponent` | `Nat.maxPowDvdDiv p n`, `padicValNat p n` | Replaced the custom loop with the existing reducible algorithm; edge cases are tested. | `padicValNat_def` and `Nat.multiplicity_eq_factorization` give the mathematical bridge; do not substitute noncomputable `multiplicity` in runtime code. |
| `isSquareMod`, `legendreValue` | `IsSquare`, `quadraticCharFun`, `legendreSym`, `jacobiSym` | Reuse symbols in specifications; retain the kernel-friendly finite square search until a public fast kernel computation is proved/available. | The fast Jacobi replacement is private and compiler-directed; its presence alone does not speed `decide +kernel`. |
| Point-count adapters | TauCeti `pointCount`, `frobeniusTrace`; extracted finite-field candidate | Keep the mathematical objects; share the new invariance lemmas instead of duplicating them. | `pointCountFinite` is a reducible alternative, but changing enumerators still needs equivalence and kernel benchmarks. |
| `GloballyMinimalInput` | TauCeti `WeierstrassCurve.IsGlobalMinimal` | Prove completion/localization compatibility, then expose the existing predicate in geometric APIs. | Not definitionally equal: different coefficient rings and quantification. |
| `SemistableModel` | TauCeti `WeierstrassCurve.IsSemistable` | Treat current gcd condition as a sufficient input-model criterion; prove the implication. | It is not equivalent for arbitrary integral equations representing a semistable curve. |
| `tameAtWild` | Existing reduction predicates and semistability | Keep/name as a guard at 2 and 3; prove its local meaning. | It neither proves global semistability nor minimality. |
| `tameLevel`, `wildLevel`, sign formulas | Intrinsic EC conductor / root number | Keep explicitly formula-valued specifications until geometric bridges exist. | No directly reusable intrinsic conductor/epsilon API was found in these pinned EC sources. |

## Invariants, equation maps and primality

Mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` defines:

```lean
-- Existing Mathlib definitions, specialized here to an integral input e.
e.c₄ = e.b₂ ^ 2 - 24 * e.b₄
e.c₆ = -e.b₂ ^ 3 + 36 * e.b₂ * e.b₄ - 216 * e.b₆
```

Those expressions were duplicated in [ReductionCore](../VerifiedLcalc/EllipticCurve/ReductionCore.lean) at the start of this audit; the duplicates have now been removed. Discriminant and b-invariants already use Mathlib directly. `map_c₄`, `map_c₆`, `map_Δ`, `map_map` and `baseChange` provide the coefficient-transport vocabulary. The project's [Correctness](../VerifiedLcalc/EllipticCurve/Correctness.lean) wrappers record specialized integer-cast consequences. They can remain small adapters, but should not become new independently maintained definitions. A replacement must preserve the theorem consumers and computational reduction behavior; the parent is implementing/checking this cleanup separately.

[Arithmetic](../VerifiedLcalc/EllipticCurve/Arithmetic.lean) already defines `isPrime p := decide (Nat.Prime p)`. Mathlib `Data/Nat/Prime/Defs.lean` supplies `decidablePrime` for kernel reduction and `decidablePrime'` with `decidablePrime_csimp` for compiled execution. The source explicitly recommends `norm_num` rather than plain `decide` for standalone large primality proofs. That is a possible proof-production improvement if the command later emits separate primality subproofs; it is not permission to introduce native verification axioms. A whole conjunction proved by `decide +kernel` still follows its kernel-reducible decision procedure.

## Valuation: existing executable algorithm and exact edge cases

The local [CoefficientCore](../VerifiedLcalc/EllipticCurve/CoefficientCore.lean) repeats division with a structural fuel bound. [Coefficients](../VerifiedLcalc/EllipticCurve/Coefficients.lean) proves `primeExponent_correct hp : primeExponent p n = n.factorization p` for prime `p`.

The existing Mathlib implementation is public and genuinely reducible:

```lean
-- Mathlib/Data/Nat/MaxPowDiv.lean
Nat.maxPowDvdDiv (p n : ℕ) : ℕ × ℕ
-- Mathlib/Data/Nat/PadicValNat.lean
padicValNat p n = (Nat.maxPowDvdDiv p n).fst
```

`maxPowDvdDiv` recursively squares the base, rather than peeling off one prime factor per recursive call. It returns an exponent and the remaining quotient. The source bounds recursion depth logarithmically in the valuation. This is an algorithmic opportunity, not a measured kernel speedup in this audit.

`padicValNat` itself is **not deprecated** at this pin. Several older theorem names bearing `padicValNat` are deprecated in favor of multiplicity names. The public bridge is `Nat.padicValNat_def : padicValNat p n = multiplicity p n`. `Nat.multiplicity_eq_factorization hp` in `Data/Nat/Factorization/Defs.lean` then identifies it with `n.factorization p` for prime `p`. The unqualified `multiplicity` and `emultiplicity` definitions in `RingTheory/Multiplicity.lean` are noncomputable specifications.

The total-input cases matter:

| Inputs | Local loop | Existing algorithm/spec |
| --- | --- | --- |
| `n = 0` | 0 | `maxPowDvdDiv p 0 = (0,0)`; `padicValNat p 0 = 0`; `emultiplicity` can instead be top. |
| `p = 0` or `p = 1` | 0 | `maxPowDvdDiv p n = (0,n)` for `p ≤ 1`. |
| prime `p`, positive n | exponent of p | Agrees with `n.factorization p` by the existing bridges. |
| composite `p > 1`, positive n | largest exponent of that composite base | `maxPowDvdDiv` has the same intended meaning; `n.factorization p` is zero, so factorization is not a total-input replacement. |

The local prime-only theorem is insufficient to justify every arbitrary-input caller if the definition changes. Either prove the total loop/`padicValNat` equality once, or establish primality at every point relying on that equality. Example edge checks should include `p=0,1,4`, `n=0,1,16`. Retain an independent mathematical specification and the per-function correctness theorem even if the custom loop disappears.

## Quadratic characters: specification reuse is clearer than a promised speedup

[The tame arithmetic adapter](../VerifiedLcalc/EllipticCurve/Tate/TameArithmetic.lean) already proves `isSquareMod_correct` and `legendreValue_correct` using `IsSquare` and `legendreSym`. The latter currently carries an extra `p ≠ 2` hypothesis although its proof only uses the ordinary zero/square/nonsquare characterization. Any removal of that hypothesis must be checked; it does not require inventing another character definition.

Mathlib `NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean` defines `quadraticCharFun` from decidable zero and square tests. For a finite field, `Data/Fintype/Parity.lean` supplies a finite existential decision procedure for `IsSquare`. Thus `legendreSym` is computable, but kernel reduction of its definition still involves finite square existence. It is not intrinsically a logarithmic algorithm in the kernel.

Mathlib `NumberTheory/LegendreSymbol/JacobiSymbol.lean` contains:

- Public `jacobiSym a b`, defined by a product over `b.primeFactorsList`.
- Public `legendreSym.to_jacobiSym`, identifying it with `legendreSym p a` for every prime p. There is no oddness hypothesis: this Mathlib definition extends the Jacobi symbol to even denominators, including p=2, using Legendre factors. At b=0 it returns 1. Do not substitute a different external convention silently.
- **Private** recursive `fastJacobiSymAux` and `fastJacobiSym`, with private correctness theorem `fastJacobiSymAux.eq_jacobiSym` and compiler simplification theorem `fastJacobiSym.eq : jacobiSym = fastJacobiSym`.
- A private `fastLegendreSym` and corresponding compiler simplification theorem.

These correctness proofs are useful upstream evidence, but the private auxiliaries are not a stable public API. Compiler simplification does not automatically rewrite a proposition while the kernel reduces `decide`. A public, theorem-linked fast computation exposed for kernel verification would be a worthwhile upstream request. The implementation now uses the generic finite-ring square decision, with correctness and edge regressions, while retaining the zero/square/nonsquare Legendre wrapper. A performance comparison remains separate. Importing `JacobiSymbol` alone is not a verified performance optimization for this certificate mode.

For nonprime p the current `legendreValue` is simply a residue-ring zero/square test, not a Legendre character; arbitrary replacement by `jacobiSym a p` changes that function. A dependent prime input or explicit validated prime guard is required if code uses the canonical prime character directly. Tame formulas invoke it only in proved prime cases.

## Already reusable TauCeti mathematics and the remaining adapters

The pinned full checkout includes minimal-model theory, `GlobalMinimalModel.lean`, `MinimalModel/Semistable.lean`, point counts (including singular solutions), node polynomials, local Euler polynomials, a formal Tate q-curve, specialization, Tate modules, modular-form L-functions, Fricke sign theory, analytic rank and uniqueness of entire L-series extensions. Reuse these objects. A file named `TateCurve` is not a complete Tate reduction algorithm.

The new generic [Minimality](../VerifiedLcalc/UpstreamCandidates/TauCeti/Minimality.lean), [TwoAdicMinimality](../VerifiedLcalc/UpstreamCandidates/TauCeti/TwoAdicMinimality.lean), and [PointCount](../VerifiedLcalc/UpstreamCandidates/TauCeti/PointCount.lean) modules separate candidates from attributed upstream ports. Their small-discriminant/c4/c6 and two-adic criteria are additional theorems in existing Weierstrass/DVR vocabulary, not replacement definitions. The EC backend imports these candidates for the generic mathematical lemmas. Its existing ZMod point enumerator remains; `pointCountFinite` is an available candidate, not yet a claim that the entire enumerator has been replaced.

Further proved-bridge work:

1. **Reduction of a supplied minimal equation.** Mathlib `AlgebraicGeometry/EllipticCurve/Reduction.lean` defines `HasGoodReduction`, `HasMultiplicativeReduction`, and `HasAdditiveReduction` as classes extending minimality. A raw discriminant/c4 congruence test does not establish these classes for a nonminimal input. Local `LocalModel.localPolynomial_of_minimal_input`, [TauCeti adapters](../VerifiedLcalc/EllipticCurve/TauCeti.lean), and reduction correctness already bridge supplied minimal equations to the chosen minimal representative. Preserve those hypotheses.
2. **Residue field identification.** [Residue](../VerifiedLcalc/EllipticCurve/Residue.lean) composes existing quotient equivalences, `Int.quotientSpanNatEquivZMod` and TauCeti `residueFieldEquivAdicCompletionIntegers`. The composition is a useful Q-specific adapter; it is not a new proof that finite prime fields are ZMod.
3. **Global coefficient extraction.** `GlobalCoefficients.LFunction_apply_prime_pow` combines existing abstract EC L-functions with rational-place uniqueness and the arithmetic Euler-product extraction theorem. Keep this Q-specific where norms are injective. A general-number-field version must group multiple places above a rational prime and account for residue degrees.
4. **Continuation uniqueness.** `Modularity/RealizationIndependence.lean` already uses Mathlib analytic uniqueness to identify supplied realizations. TauCeti `NumberTheory/LSeries/EntireExtension.lean` supplies a higher-level `LSeries.HasEntireExtension.unique` API. Replacing the short local proof is optional integration, not missing mathematical theory or an axiom-elimination milestone.

## Similar names that are not interchangeable

### Global minimality

Current `GloballyMinimalInput e` quantifies over ordinary rational primes and asserts minimality over their completion integer rings. TauCeti's existing:

```lean
WeierstrassCurve.IsGlobalMinimal O W
-- unfolds to minimality over Localization.AtPrime v.asIdeal,
-- for every v : HeightOneSpectrum O, with [W.IsElliptic].
```

is a localization-based predicate on a fraction-field curve, with ellipticity in its type. It has integrality and integral-change-of-variables consequences. They should be the eventual public geometric interface. To connect the current condition, prove local minimality transfer between localization and completion, align the Q prime indexing, and instantiate ellipticity from nonzero discriminant. No such complete bridge was identified by this targeted audit. Do not replace one predicate by the other via a definition alias or add an axiom asserting the equivalence.

### Semistability

Current `SemistableModel e` means `Int.gcd e.Δ e.c₄ = 1`. TauCeti `MinimalModel/Semistable.lean` defines `WeierstrassCurve.IsSemistable O W` by no additive reduction on each local **minimal** equation and proves characterizations through good/multiplicative reduction and valuations. This is intrinsic under variable changes.

The gcd condition refers to the particular integral equation. An integral nonminimal scaling of a semistable curve can make both invariants divisible by a prime, so intrinsic semistability does not imply that condition for every input equation. The gcd condition alone also lacks nonsingularity: the integral equation `y² + xy = x³` has Δ=0 and c4=1, hence gcd(Δ,c4)=1, whereas TauCeti’s intrinsic predicate requires `[W.IsElliptic]`. Any implication must therefore include the curve’s nonzero-discriminant hypothesis. First prove the sufficient implication using the local minimality/reduction lemmas. An equivalence requires appropriate input minimality and localization/completion compatibility. Name an input criterion as such; do not advertise it as the definition of intrinsic semistability.

### Guard at the wild primes and formula-valued conductor/sign

`tameAtWild e` excludes additive reduction at 2 and 3 for the tested equation. It says nothing about additive places at p≥5 and does not prove the equation minimal. `NegativeJValuation` uses factorization valuations and a c4 nonzero guard; relating it to the valuation of intrinsic `W.j` needs the nonzero discriminant and cast/valuation identities. Removing the guard changes the j=0 case because the Nat-valued convention gives valuation zero at zero.

`tameConductorExponent`, `tameLevel`, `wildLevel`, `tameSign`, and `wildSign` are arithmetic formulas. Their correctness theorems identify computations with those formulas. They are not definitions of geometric conductor or epsilon factors whose correctness follows merely by naming them that way.

## Missing intrinsic conductor/root-number interfaces

A targeted declaration/content search of the full pinned elliptic subtrees, plus searches for Artin/Swan conductor, epsilon factor and local root-number APIs across the pinned libraries, found no directly reusable elliptic-curve intrinsic conductor/root-number package. Generic Dirichlet L-function root-number material is a different subject. This is a scoped negative finding, not a claim that no relevant theory exists on another branch.

Required bridges still include:

- A geometric/representation-theoretic local conductor exponent, its tame/wild decomposition, and agreement with the validated Tate/Ogg expression.
- Local epsilon/root numbers with explicit normalization and their identification with the tame and wild formulas, including Halberstadt cases at 2 and 3.
- Global product formulas and the equality of arithmetic conductor with the normalized newform level, and of global root number with its Fricke functional-equation sign.

The authorized [general modularity assumption](../VerifiedLcalc/Assumptions/Modularity.lean), through [ArithmeticRealization](../VerifiedLcalc/EllipticCurve/Modularity/ArithmeticRealization.lean), still supplies these arithmetic normalization conclusions conditionally. Extracting local minimality and point-count theorems does not remove it. None of the interface reuse above proves small derivatives are exactly zero; [precision hypotheses](../VerifiedLcalc/Assumptions/Precision.lean) remain a separate, explicitly indexed boundary.


## Focused follow-up: `LocalModel.lean` versus the complete minimal-model API

The follow-up inspected [LocalModel](../VerifiedLcalc/UpstreamCandidates/TauCeti/LocalModel.lean), Mathlib `AlgebraicGeometry/EllipticCurve/Reduction.lean`, and the **full** pinned TauCeti `AlgebraicGeometry/EllipticCurve/{IntegralModel,MinimalModel/Basic,LocalPolynomial}.lean`. The selected `MinimalModel/Basic` port omits some later declarations, but already includes the minimal-model comparison and unit-scaling lemmas used here. The following distinctions avoid either reproving existing results or deleting a necessary bridge.

| Local declaration | Exact reusable ingredients | Recommendation |
| --- | --- | --- |
| `integralModel_eq_of_baseChange` | Mathlib `baseChange_integralModel_eq`, `map_injective`, `IsFractionRing.injective` | Already a small convenience corollary, not a replacement definition. Keep or extract as a generic Mathlib lemma; no exact named counterpart was found. Its current statement already omits unnecessary DVR assumptions. |
| `valuation_eq_one_of_unit` | Mathlib `Valuation.Integers.one_of_isUnit'` plus `HeightOneSpectrum.valuation_le_one` | Directly shorten the local proof, or call the existing valuation lemma at its consumers. |
| `isMinimal_of_unit_discriminant` | Mathlib `IsMinimal`/`valuation_Δ_aux` API; extracted `minimal_of_small_discriminant` | No exact named unit-discriminant criterion was found in the inspected upstream files. It can become a corollary of the stronger extracted criterion after supplying its normalized valuation/integer-ring hypotheses; otherwise the current elementary proof is legitimate. |
| `isMinimal_of_unit_invariants` | Previous unit-Δ criterion; TauCeti `isMinimal_of_valuation_c₄_eq_one` | The c4 branch already reuses that exact TauCeti theorem. Keep this as a union-of-sufficient-criteria convenience lemma, rather than presenting it as missing c4 theory. |
| `reduction_eq_variableChange` | TauCeti `exists_smul_eq_minimal`, `VariableChange.exists_unit_algebraMap_eq_u_of_isMinimal_smul`; Mathlib `variableChange_integral_of_u_integral` | Already uses the comparison theory. Full TauCeti `VariableChange.exists_baseChange_eq_of_smul_eq` can package the descent step but does not itself supply the final residue-model equality. |
| `localPolynomial_of_minimal_input` | Previous reduction bridge; TauCeti `variableChange_frobeniusTrace`, `localPolynomial_eq_of_hasGoodReduction`, `localPolynomial_eq_of_not_hasGoodReduction`; Mathlib reduction/ellipticity and discriminant-map API | Retain/extract as a useful generic supplied-minimal-model theorem. No exact complete counterpart was found in the pinned sources. |

The exact unit-valuation API, in `Mathlib/RingTheory/Valuation/Integers.lean`, is more general than a DVR:

```lean
-- Existing theorem; surrounding ring/algebra/valuation parameters omitted.
Valuation.Integers.one_of_isUnit'
  (hx : IsUnit x)
  (H : ∀ x, v (algebraMap O R x) ≤ 1) :
  v (algebraMap O R x) = 1
```

Accordingly the current wrapper should admit the short proof shape
`Valuation.Integers.one_of_isUnit' hx (fun x => valuation_le_one _ _)`.
This is a source-based proposed proof, not a claimed elaboration/build result. The stronger variants `Valuation.Integers.one_of_isUnit`, `isUnit_iff_valuation_eq_one`, and `valuation_unit` require an explicit `v.Integers O` hypothesis; use them when that hypothesis is already available. The primed theorem avoids constructing that extra record just for this implication.

For comparison/descent, full TauCeti `MinimalModel/Basic.lean` supplies:

- `valuation_Δ_le_of_isMinimal_smul`, `valuation_Δ_eq_of_isMinimal_smul`, and `isMinimal_of_valuation_Δ_eq_of_isMinimal_smul`.
- `isMinimal_baseChange_smul`, `valuation_u_eq_one_of_isMinimal_smul`, and `VariableChange.exists_unit_algebraMap_eq_u_of_isMinimal_smul`.
- Later, `valuation_Δ_minimal_smul`, `valuation_c₄_minimal_smul`, and `HasSplitMultiplicativeReduction.of_isMinimal_smul`.

The full `IntegralModel.lean` adds the following descent interface (with the integrally-closed-in ambient assumptions):

```lean
-- Existing theorem; R/K ambient typeclass assumptions omitted.
VariableChange.exists_baseChange_eq_of_smul_eq
  [IsIntegral R W₁] [IsIntegral R W₂]
  (D : VariableChange K) (hD : D • W₁ = W₂) (u₀ : Rˣ)
  (hau : algebraMap R K ↑u₀ = ↑D.u) :
  ∃ C₀ : VariableChange R, C₀.baseChange K = D
```

Its `IsIntegrallyClosedIn` scope is broader than the DVR setting. The current Mathlib `variableChange_integral_of_u_integral` already handles the DVR situation used by `LocalModel`; importing an additional large file solely to trade one descent call for another is not automatically beneficial. The actual residue-field variable change and invariance of the trace still have to be derived.

Minimality does not make Mathlib's arbitrarily chosen `W.minimal R` definitionally equal to the caller's equation. The integral models are related by an invertible variable change, which may produce singular residue equations. Preserving this distinction is why `reduction_eq_variableChange` and the supplied-input local-polynomial theorem remain useful even when all comparison machinery is imported. Neither a split-multiplicative transfer theorem nor equality of discriminant valuations by itself states the full local-polynomial equality.

## Acceptance gates for the proposed replacements

Apply one family at a time. Retain old-to-new equality theorems or prove total-input equivalence; preserve arithmetic axiom audits; check ordinary theorem and import-only consumers. For changes intended to improve validation, measure the `decide +kernel` path separately from compiled evaluation, including previously expensive witness inputs. The root agent is the sole build owner; this audit's static source findings do not substitute for those checks. No source imports, implementation or build configuration were changed by this document.


## Applied follow-up: shared evaluation and smaller correctness interface

The backend now uses the generic finite-ring count and trace evaluator in
`UpstreamCandidates/TauCeti/PointCount.lean`. Prime-field correctness connects
it to TauCeti's existing mathematical definitions. The bespoke integer-modulo
point enumeration, `residueEquiv`, solution-subtype conversion and manual list
counting proofs have been removed. The redundant coefficient/base-change/map
wrappers now use Mathlib directly. Modularity's good-prime compatibility and
semistable sign formula use the canonical mathematical Frobenius trace;
computational compatibility is derived, rather than assumed separately.

`Correctness.lean` now contains only five project-specific results:

| Result | Purpose |
| --- | --- |
| `isPrime_correct` | Reflect the backend's Boolean prime filter. |
| `goodReduction_correct` | Reflect its Boolean discriminant test. |
| `computePointCount_correct` | Specialize shared finite counting to integer input and prime modulus. |
| `computeFrobeniusTrace_correct` | Specialize shared finite trace to the canonical TauCeti trace. |
| `analysePrime_sound` | Assemble the backend record's guarantee using the preceding bridges. |

The LocalModel recommendations above have been applied: the unit-valuation
wrapper was removed in favor of Mathlib's primed theorem, and the single-use
integral-model equality was inlined. The four substantive remaining bridges
were extracted into the `WeierstrassCurve` namespace in
`UpstreamCandidates/TauCeti/LocalModel.lean`; the production adapter file was
deleted. Earlier source-only recommendations above record the audit that led
to this change. These extractions do not solve the global-minimality
localization/completion comparison or conductor/epsilon-factor obligations.


## File-by-file cleanup follow-up

The [file-by-file audit](ELLIPTIC_CURVE_FILE_AUDIT.md) records the latest queue and
its application. In particular, `isSquareMod` and `legendreValue` are now gone:
the tame additive evaluator validates primality and uses Mathlib's
`legendreSym`, while the wild table uses Mathlib's three primitive characters.
The unsupported nonprime tame-additive branch returns zero. The old
all-nonzero-modulus square adapter is no longer needed by production code;
finite square tests call `IsSquare` directly. No compiled-only shortcut is used.

`ModelEulerFactor`, `localSeries`, the duplicate recurrence specification,
handwritten integral translations, `TateDiv`, and the prime-product induction
were removed as well. The canonical inverse polynomial and its coefficients
now specify the executable coefficient routine directly. The application does
not remove or expand the authorized modularity assumption.

The last modularity pass also removes the `gamma0` coercion wrapper and
redundant arithmeticity/width/normalization assumption fields. Existing Mathlib
Gamma0 instances and width lemmas supply the first two properties; matching
all curve coefficients forces normalization via `LFunction_apply_one`.


## Canonical global minimality integration

The earlier TC-04 adoption blocker has been bypassed with a direct witness
proof, not an assumed comparison theorem. The canonical TauCeti global-minimal
predicate and its localization API are now selected ports. The handwritten
`GloballyMinimalInput` definition is gone; conductor/sign compatibility takes
`WeierstrassCurve.IsGlobalMinimal (𝓞 ℚ)` directly. Checked finite criteria prove
minimality over those localizations, and the existing independent completion
proof still supplies numerical coefficient correctness. The full comparison
between arbitrary localization and completion minimality remains unproved.
