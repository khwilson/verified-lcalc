# Exact rank one from a first derivative

The derivative backend uses the existing general modularity assumption and adds
no numerical or exact-vanishing axiom. All interval, quadrature, Fourier-tail and
Mellin differentiation proofs depend only on Lean/mathlib's standard axioms.
`AuditDerivative.lean` guards that dependency boundary.

For a negative-sign modular realization, write alpha = 2*pi/sqrt(N). The functional
equation gives exact central vanishing, and differentiation of the Mellin
transform gives

    Re L'(1) = 2*alpha * integral_[1,infinity) log(t)*Re f(i*t/sqrt(N)) dt.

The proof differentiates the Mellin transform using the cusp bounds, applies the
Fricke substitution to the logarithm-weighted integrand, and cancels the derivative
of the normalization using exact central vanishing. It needs no numerical gamma
derivative. A nonzero enclosure of this integral, together with analyticity,
proves that the central zero has order exactly one.

## Verified numerics

`DerivativeCore.lean` computes rational outward enclosures. Each integration cell
uses exponential bounds from the existing Ledvinka dyadic implementation and a
rounded interval Horner evaluation of the Fourier prefix. The coefficient bound
`|a_n| <= n^3` supplies a geometric majorant for the omitted terms. Multiplication
handles either sign of the Fourier prefix. Logarithms use the atanh series with
an explicit positive remainder, followed by outward dyadic rounding.

The finite interval is partitioned into rational cells. A separate theorem sums
their integral enclosures. Beyond the cutoff T, `log(t) <= t` and exponential
decay give the absolute bound

    2*T/alphaLo * Q/(1-8*Q),

where Q bounds exp(-alpha*T), with checked conditions alphaLo*T >= 2 and 8*Q < 1.
The proof establishes integrability and the infinite-tail inequality.

The stored box bounds the normalized integral J. `realDerivativeBounds` multiplies
it by an outward enclosure of 2*alpha; its correctness theorem bounds the actual
real part of L'(1). Precision follows the global policy (53 bits). The Fourier
length, cell count and cutoff are separate adaptive parameters. Failure to
separate zero remains inconclusive, regardless of a reference rank or tolerance.

## Certificates and cache

`derivative-batch` reads only fixture input projections and proposes candidates.
`certify-derivatives` rebuilds their Lean proof bundles, checks each finite payload
in the kernel, and installs the rank-one registry only after its subject-bound
soundness theorem compiles. The resulting theorem concerns the canonical modular
witness for that exact equation. Saved consumers execute a subtype whose value is
one and whose proof establishes that analytic order.

When inputs yield identical numerical payloads apart from the curve equation,
the generator reuses the earlier interval-computation theorem. Each new curve's
coefficient identification is checked separately, and its analytic theorem still
concerns its own equation. This avoids repeating the same kernel arithmetic for
isogenous curves. Replay runs at most two numerical proof bundles concurrently
to limit memory pressure.

`certify-derivatives --seal-cache` checks subjects and source hashes, rebuilds the
proof dependency graph, and reuses checked `.olean` artifacts for unchanged
sources. A changed dependency triggers rechecking. Hashes identify artifacts;
they do not replace the Lean proof. Registry installation restores sources and
rebuilds the preceding compiled artifacts if a binding is rejected.

The rank-zero and rank-one reports remain separate. The combined strict regression
checks the installed backend against all 1,100 external reference records and
fails whenever any curve remains inconclusive. Reference ranks never enter
certificate production or proof construction.

```sh
lake exe certify-derivatives
lake env lean certificates/Derivative.lean
lake env lean AuditDerivative.lean
lake exe certify-derivatives --seal-cache
```

The producer/installer commands finish with the strict combined regression. Its
exit status is 1 while any fixture remains inconclusive, even if certificate
installation succeeded. A rejected proof or registry installation exits 2.

## Regression coverage

The 1,100-input run produces 228 checked exact rank-one certificates out of the
229 curves with checked negative-sign evidence. Together with the existing 822
rank-zero certificates, the combined backend has 1,050 matches, zero mismatches
and 50 inconclusive inputs. These analytic claims are conditional on the single
existing general-modularity assumption; no new assumption was added.

The remaining inputs are 48 curves without a proved minimality criterion,
389.a1 whose central interval contains zero, and 5077.a1 whose first-derivative
interval contains zero. The negative sign still proves a rank lower bound for
5077.a1. Reference ranks do not resolve either numerical enclosure.
