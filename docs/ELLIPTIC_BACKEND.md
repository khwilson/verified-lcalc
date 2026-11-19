# Elliptic-curve backend status

Workflow status (2026-11-19): legacy batch/derivative/conductor generators,
`lmfdb-check`, generated registries and bulk certificate directories described
below have been retired. Their command examples and cache counts are historical,
with implementation preserved in baseline commit `fcdc4f2`. The mathematical
proof engine remains; use [`certify_ec`](CERTIFY_EC.md) for current witness
verification and importable theorem generation.

The backend now performs exact good-prime arithmetic, model Euler coefficient
prefixes, and central exponential-expression interval evaluation. It is not yet
a backend for analytic ranks. The [central evaluator](CENTRAL_EVALUATOR.md)
records its implemented proofs, executable, replayable payloads and remaining
elliptic interpretation obligations.

```sh
lake build
lake exe ec-coefficients --curve 11.a2
lake exe ec-coefficients --summary
lake env lean tests/VerifiedLcalcTests/Fixtures/Curve11Arithmetic.lean
```

## Implemented and proved

`EllipticCurve/Arithmetic.lean` is executable using Std/Init and the existing
exact input type. It implements integral Weierstrass invariants, the
discriminant, exact modular equation testing, exhaustive affine-point enumeration,
projective point counts, Frobenius traces, primality testing, and good-reduction
testing. Characteristics 2 and 3 use the full Weierstrass equation. Infinity is
counted exactly once. There is no floating-point arithmetic.
The exhaustive point counter is an O(p²) reference implementation for small
primes, not yet a fast large-prime point-counting algorithm.

`EllipticCurve/Correctness.lean` connects each routine to mathlib:

- Invariants and discriminants agree with the actual Weierstrass model.
- The modular predicate is equivalent to mathlib's affine equation.
- Enumeration is complete and duplicate-free.
- The computed count is the cardinality of the equation-solution subtype plus
  infinity; at good primes it is the cardinality of mathlib's curve-point type.
- Trial division is equivalent to `Nat.Prime` and the discriminant test proves
  that the reduced model is elliptic.
- `analysePrime_sound` gives the actual mathematical point count and trace for
  every successful call, for arbitrary exact input coefficients and primes.

The runtime `localPair` computes the local prime-power recurrence in linear time.
`localCoefficient_correct` and `localCoefficient_unique` prove its specification
and uniqueness. `Euler.lean` proves that the generated series is the inverse of
`1 - a*T + q*T^2`, including linear factors when q=0. This does not yet identify
the whole computed coefficient sequence with mathlib's global `LFunction`.

`Certificates/Curve11Arithmetic.lean` is an actual elliptic-curve arithmetic
certificate: the 11.a2 model has five F₂-points, trace -2, and the computed local
series inverts its good Euler polynomial. It imports kernel-checked computation
equations and the universal arithmetic soundness theorems. It makes no analytic
rank claim. Further examples test primes 2, 3, 5, 7, rejection of composite and
bad primes, degenerate models, and good/linear Euler recurrences.

The executable uses only the exact coefficients from each LMFDB input. The
stored expected rank is never passed to arithmetic. Its fixture run attempts
nine small primes on each of the 100 curves and reports good-prime successes and
bad-prime cases separately. Its exit status is a computation/smoke-test status,
not a successful analytic-rank comparison. `lmfdb-check` remains the strict rank
gate and still fails with unresolved analytic ranks.

The recorded fixture smoke run on 2026-11-17 completed 720 good-prime
calculations and reported 180 bad-prime cases pending, across all 100 curves.
The build, fresh arithmetic-certificate replay, existing certificate replays,
and axiom audit passed. The strict rank gate still reports 100 inconclusive
curves and exits 1, as intended.

## Remaining work

1. Bad-prime minimal models and local factors, including proof of minimality.
   Good reduction of the supplied model is currently required; an isomorphic
   nonminimal model is not silently treated as minimal.
2. Identify the implemented multiplicative model coefficients with the actual
   curve's global Euler coefficients. Finite coefficient computation and its
   prime-factorization proof are now implemented; the curve identification
   still needs minimality and the local-factor theorems.
3. Entire continuation of the curve's series, normalization, and its relationship
   to a weight-two modular form or another rigorously established continuation.
4. Certified special-function evaluation and explicit tail/derivative bounds.
   Basic dyadic intervals and proved exponential bounds now reuse Ledvinka's
   work. Signed finite exponential sums and composition with a proved tail
   estimate are implemented. Log/gamma evaluators, the elliptic central-value
   formula and derivative estimates remain outstanding. Central-expression
   argument, finite-sum and geometric tail bounds are now proved, with explicit
   series-evidence obligations for the actual L-value.
5. Exact vanishing arguments, especially beyond ranks 0 and forced rank 1.
6. Analytic enclosure artifacts, end-to-end rank certificates, and the 100-curve
   strict rank regression.

The subject interpretation still refuses elliptic analytic certificates until
the missing definition and proofs are supplied. No axiom, numerical tolerance,
LMFDB lookup, raw divergent-series value, or arbitrary substitute function has
been used to bypass this requirement. [Infrastructure findings](INFRASTRUCTURE.md)
identify existing TauCeti modules for several of the remaining mathematical steps.

## Opt-in modularity assumption

The user has authorized a single temporary modularity axiom. A separate
[assumption-dependent interface](ASSUMPTIONS.md) supplies a genuine cusp-form
realization with actual Euler coefficient matching and Fricke symmetry. It
provides entire continuations and certificate interpretations conditional on
that axiom. The default subject interpretation and numerical evaluator remain
independent of the assumption. The central split-Mellin integral and negative-sign central vanishing are now
proved from a supplied realization; the conditional 37.a1 certificate gives
analytic rank at least one. The central exponential-series and interval-enclosure connection are now
proved with an explicit arithmetic prime-power compatibility input. Global Euler-product extraction and the actual coefficient bound are now
proved. A concrete conditional rank-zero certificate for 11.a2 supplies its
finite prefix. General input-model identification and derivative evaluation
remain required.
See [INTEGRATION.md](INTEGRATION.md).
