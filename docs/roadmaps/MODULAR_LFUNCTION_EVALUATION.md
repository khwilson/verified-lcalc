# Modular L-function evaluation: reusable analytic theorems

Companion to [the audit and version matrix](../TAUCETI_ROADMAP.md). Generic analytic results should depend on a supplied modular form and explicit hypotheses, not the custom elliptic-modularity axiom. Exact rank statements obtained by selecting the canonical elliptic realization may still depend on that axiom. Proposed generalizations below have not been compiled as new declarations.

## Existing infrastructure to consume

At the inspected TauCeti pin:

| File below `TauCeti/` | Existing declarations / role |
| --- | --- |
| `NumberTheory/LSeries/EntireExtension.lean` | `LSeries.HasEntireExtension`, existence and uniqueness of continuation, including `unique` and `existsUnique` |
| `NumberTheory/ModularForms/LFunction/Basic.lean` | `LSeries_qExpansion_coeff_eq`, cusp-form entire extension, nontrivial L-function and finite analytic order from a nonzero coefficient |
| `NumberTheory/ModularForms/LFunction/FunctionalEquation.lean` | `resToImagAxis_slash_frickeGL`, `frickeCompletedL_eq_cpow_mul_Λ`, `frickeCompletedL_functional_equation` |
| `NumberTheory/ModularForms/LFunction/Sign.lean` | Normalized Fricke eigenvalue/sign identities and forced central vanishing; `analyticRank_pos_of_I_zpow_mul_frickeSign_ne_one` |
| `NumberTheory/ModularForms/Newforms/AnalyticInvariants.lean` | Analytic rank as a natural number, finite order, and rank zero / positive characterizations |

Mathlib already supplies modular-form `L`, Mellin transforms, gamma identities and analytic-order characterizations. Reuse these definitions rather than introducing a second L-function or rank type. TauCeti's [modular-form roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/ModularForms/README.md) owns this analytic continuation/Fricke setting; the [L-function roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/LFunctions/README.md) supplies a broader Mellin/functional-equation setting. These are existing workstreams, not missing foundations to rebuild.

A1 is an immediate adapter opportunity: [RealizationIndependence](../../VerifiedLcalc/EllipticCurve/Modularity/RealizationIndependence.lean) proves `ModularRealization.formL_eq` and `analyticOrder_eq` using continuation uniqueness. Route it through the existing `HasEntireExtension.unique` where compatible. Agreement of Dirichlet coefficients plus continuation is sufficient; the chosen modular realization need not be definitionally unique. Acceptance: no custom modularity axiom when the two realizations are supplied as arguments.

## A2: central evaluation, split into two PRs

First extract the generic change-of-variables lemma from [MellinSplit](../../VerifiedLcalc/Numerics/MellinSplit.lean) to Mathlib's Mellin API:

```lean
-- Existing local signature; open Set MeasureTheory.
theorem mellin_one_split (f : ℝ → ℂ) (w : ℂ)
    (hf : MellinConvergent f 1)
    (hfeq : ∀ t : ℝ, 0 < t → f (1 / t) = w * (t : ℂ) ^ 2 * f t) :
    mellin f 1 = (1 + w) * mellin ((Ioi (1 : ℝ)).indicator f) 1
```

This lemma is not elliptic-curve theory. Check whether the current Mellin functional-equation API already makes it a short corollary. Keep the inversion normalization explicit.

Second generalize [CentralIntegral](../../VerifiedLcalc/EllipticCurve/Modularity/CentralIntegral.lean), [Fourier](../../VerifiedLcalc/EllipticCurve/Modularity/Fourier.lean) and [CentralSeries](../../VerifiedLcalc/EllipticCurve/Modularity/CentralSeries.lean) to a weight-two cusp form. The input should be the existing `CuspForm` type at an appropriate Γ0(N), positive N, its Fricke relation, real Fourier coefficients `a n`, zero constant term, and an explicit summable growth majorant. Avoid a new “EC series” structure containing the desired conclusion.

With `F(t) = f(i t / √N)`, `α = 2π / √N`, functional-equation sign `w`, and the arithmetic L-function normalization, the intended real-valued output is:

```text
HasSum (j ↦ (1 + w) * a(j+1)/(j+1) * exp(-α*(j+1))) (L(f,1)).re
```

The current local theorem uses `|a n| ≤ n^3`. Start with that sufficient hypothesis, then generalize its exponent/constant if justified by a second consumer. Separate the analytic series/integral theorem from the EC coefficient-identification adapter. A normalized Fricke eigenvalue is not automatically the functional-equation sign: keep the weight-two normalization factor visible.

Acceptance: derive integrability, justify swapping sum and integral, prove the formula for a supplied form, and recover the existing EC theorem using its coefficient bound. Test the sign factors by deriving exact vanishing for negative functional sign and the correct factor two for positive sign. A positive sign by itself gives no nonvanishing theorem.

## A3: first derivative and the gamma cancellation

[FirstDerivative](../../VerifiedLcalc/EllipticCurve/Modularity/FirstDerivative.lean) already proves:

- `mellin_first_derivative`: log-weighted integrability and the derivative of the Mellin transform at 1.
- `mellin_log_upper`: the negative-sign reduction to twice the integral on `(1,∞)`.
- `formL_scaled_mellin`: the normalization relating Mellin and the arithmetic L-function.
- The following exact final formula for a supplied realization:

```lean
-- Existing local signature; namespace/open declarations omitted.
theorem ModularRealization.deriv_one_re_integral
    {e : WeierstrassCurve ℤ} (m : ModularRealization e)
    (hw : m.rootNumber = -1) :
    (deriv m.formL 1).re = (4 * Real.pi / Real.sqrt m.level) *
      ∫ t : ℝ in Ioi 1, Real.log t * (m.imaginaryFunction t).re
```

Generalize the supplied-realization argument to the same modular-form inputs as A2; use Mathlib’s `WeierstrassCurve ℤ` for the local adapter and the generic cusp-form type in TauCeti. The main proof obligations are local uniform domination for differentiation under the integral, inversion of the log moment, and normalization at 1. Negative sign makes the undifferentiated Mellin transform exactly zero, canceling the derivative of the gamma/level prefactor. **Rank-zero/rank-one evaluation therefore does not require a certified numerical gamma derivative.**

Acceptance: generic theorem independent of `ellipticModularity`; the current derivative evaluator becomes an adapter; nonzero derivative plus the exact sign-forced central zero proves order exactly one through existing Mathlib analytic-order lemmas.

## A4: higher derivatives and quantitative integration

Build in this dependency order:

1. Prove an `n`th Mellin derivative theorem: the derivative is the integral with kernel `(log t)^n * t^(s-1)`, under explicit local domination hypotheses. Prefer a Mathlib theorem for general Mellin transforms, not just cusp forms.
2. Establish the hypotheses for cusp forms and quantitative coefficient bounds. Export log-moment integrability, upper/lower splitting and the parity rule under inversion.
3. Relate derivatives of `L(s) = K(s) M(s)` to Mellin moments by Leibniz. If all lower derivatives vanish exactly and `K(1) ≠ 0`, the first surviving derivative only needs `K(1)` times the corresponding Mellin derivative. Prove this cancellation generically before implementing gamma-derivative interval machinery.
4. Generalize certified tail estimates and quadrature to log powers. State dependence on derivative order, coefficient majorant and truncation explicitly. Add numerical finite witnesses only after the real/complex analysis theorem exists.

[`mellin_iteratedDeriv_of_isBigO_rpow`](../../VerifiedLcalc/Numerics/MellinLogMoments.lean)
proves convergence and the log-moment formula for every order inside the
original strict strip. The induction uses a slightly narrower strip for each
additional log weight. For the scaled cusp form (f(it/\sqrt{N})), the
[central split](../../VerifiedLcalc/EllipticCurve/Modularity/SecondDerivative.lean)
gives (M''(1)=(1+\varepsilon)\int_1^\infty (\log t)^2f(it/\sqrt{N})\,dt).
The gamma and level prefactor cancels out of the lower terms in the
second-derivative product rule only when (M(1)=M'(1)=0) exactly.
The factor at the center is (2\pi/\sqrt{N}). The leading Taylor
coefficient is the corresponding raw derivative divided by (2!).

[DerivativeTail](../../VerifiedLcalc/Numerics/DerivativeTail.lean) currently provides `fourier_tail_pointwise` and `derivative_tail_error` for the first log moment using the weak cubic coefficient bound. This is an initial theorem family, not a general arbitrary-derivative backend. [ExponentialIntegral](../../VerifiedLcalc/Numerics/ExponentialIntegral.lean) contains reusable integral and dominated-series lemmas; move genuinely general parts to Mathlib and the modular quantitative corollaries to TauCeti.

Acceptance: an explicit error bound for each requested order; interval enclosures prove statements about actual `iteratedDeriv` in the arithmetic L-normalization; no appeal to LMFDB reference ranks; no exact equality inferred from containment in a small interval. Higher-order tails may be expensive even when the elliptic equation is small.

## N1: interval exp/log belongs to numerical analysis

The current representation already uses `Set.Icc`: [RealInterval](../../VerifiedLcalc/Numerics/RealInterval.lean) defines `Contains` by membership in the real closed interval determined by rational endpoints. Do not introduce a second abstract `Box` theory for upstream number theory.

`logBounds_sound` encloses `Real.log` for rational input at least one. It uses existing Mathlib inequalities `Real.sum_range_le_log_div` and `Real.log_div_le_sum_range_add` in `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`. Rational rounding, addition, multiplication and quadrature have local inclusion theorems. Separate generic inclusion rules from the backend's policy and serialization.

The exponential inclusion proof is the attributed [Ledvinka port](../../VerifiedLcalc/Upstream/LedvinkaExponential.lean), with its [small core](../../VerifiedLcalc/Upstream/LedvinkaExponentialCore.lean). Coordinate with the author and current mathlib interval developments before proposing another API. An integer search helper named `expLogSearch` is not a certified `Real.log` evaluator. This audit found no reason to claim that the port provides gamma or general logarithm support.

An upstream numeric PR should use Mathlib's interval conventions, prove inclusion for all valid inputs and explicit domain failures, and retain attribution. Certificate-specific precision selection and finite payload formats stay here. Formal incomplete-gamma identities (already present in TauCeti's `Analysis/SpecialFunctions/IncompleteGamma.lean`) do not themselves supply executable certified interval gamma values.

## V1: numerical smallness versus exact vanishing

This mathematical gap is independent of modularity, Tate reduction, and interval rounding. The new [NumericalRankSeparation](../../VerifiedLcalc/NumericalRankSeparation.lean) defines the explicit hypothesis:

```lean
def NonzeroDerivativeGap (f : ℂ → ℂ) (center : ℂ) (n : Nat) (gap : Rat) : Prop :=
  ∀ k < n, iteratedDeriv k f center ≠ 0 →
    (gap : ℝ) ≤ |(iteratedDeriv k f center).re| ∨
      (gap : ℝ) ≤ |(iteratedDeriv k f center).im|
```

Given coordinatewise derivative smallness with cutoff `eps`, the strict inequality `eps < gap` turns this hypothesis into exact vanishing of the prefix. Analyticity then gives order at least `n`; a nonzero `n`th derivative gives exact order `n`. Mathlib already supplies `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` and `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero`. The current rational, coordinatewise separation wrappers should stay local; only a broadly reusable generalization would justify a new upstream theorem. Proving the separation hypothesis is new arithmetic, not numerical analysis.

For finitely many fixed derivatives a positive separation can exist abstractly; that does not produce an effective usable gap above a chosen global cutoff. There is no asserted universal numerical cutoff here. Raw derivatives, completed derivatives, Taylor coefficients and period-normalized values have different scales. State the convention and curve identity in every conditional claim.

The [curve-specific interface](../../VerifiedLcalc/Assumptions/Precision.lean) records the equation, precision policy, derivative count and gap. Any assumed instance must remain opt-in, indexed by that claim and visible in the resulting theorem dependencies. There is no automatically installed gap axiom. A checked interval artifact is also insufficient without semantic evidence identifying its enclosures with the true derivatives. These new interfaces were under active implementation during this source audit; the parent build owner must report their actual build result separately.

Possible future discharge routes include exact arithmetic formulas or suitable algebraicity/nonvanishing lower bounds for specifically normalized special values. Higher derivative separation is not supplied merely by modularity or the Weil conjectures. The roadmap does not assume BSD or claim a general rank-four vanishing criterion. Until a mathematical proof is supplied, conditional higher-rank conclusions must retain the curve-specific hypothesis.

## PR checklist

For A1–A4: use a consistent target revision; check for existing stronger theorems first; state convergence hypotheses explicitly; prove all exchanges of limits/integrals; verify the central point and normalization constants; audit custom axioms; replace local proofs with thin adapters. For numerical PRs also verify rounding/domain handling against the mathematical specification. For V1 distinguish proving the elementary conditional bridge from proving its arithmetic premise. No Lean build was run by this document-only audit agent.
