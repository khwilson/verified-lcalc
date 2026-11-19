# Mathematical contract and remaining implementation

For an elliptic curve E/ℚ, the intended final theorem is

```
analyticOrderAt (ellipticCurveL E) 1 = (result.rank : ℕ∞)
```

where `ellipticCurveL` is a mathematically defined analytic continuation of the
curve's L-series, with proved connection to the Euler coefficients computed from
the input Weierstrass equation. This definition and its backend are **not yet
implemented**. An arithmetic center of 1 corresponds to lcalc's unitary center
of 1/2; a formal normalization theorem will be required.

The current theorem is generic in a genuine `f : ℂ → ℂ` and center. It requires
`AnalyticAt ℂ f center` and `Encloses boxes (fun k => iteratedDeriv k f center)`.
Enclosure proofs cannot be replaced by recording lcalc/LMFDB answers, guessed
Taylor coefficients, or hypotheses silently asserted as axioms. The polynomial
demonstration supplies these proofs unconditionally. No L-function demonstration
currently does.

## Upstream audit

Sage's linked file is a Cython wrapper:
https://github.com/sagemath/sage/blob/develop/src/sage/libs/lcalc/lcalc_Lfunction.pyx

Its `compute_rank` delegates to `_compute_rank`, which in turn calls lcalc.
The Sage package metadata identifies lcalc 2.1.0:
https://github.com/sagemath/sage/blob/develop/build/pkgs/lcalc/package-version.txt
https://github.com/sagemath/sage/blob/develop/build/pkgs/lcalc/checksums.ini

The inspected archive is
https://gitlab.com/-/project/12934202/uploads/679cb360a06a713233876cd6fa0ba2fa/lcalc-2.1.0.tar.xz

SHA-256, checked against the downloaded archive:
`eca4f7de5f1129a9cec2cd2f012a8362c8489e746f07adae3229dd8eb2541f79`.

The implementation is `src/libLfunction/Lfind_zeros.h`, lines 210–280.
It first compares the central absolute value against 10^-5, then estimates the
order using nearby absolute values and logarithmic ratios, rounded to an integer.
It uses offsets 10^-5 and 10^-3, and an adaptive search with additional thresholds.
`verify_rank` calls the same estimator and compares the result. It is not an
independent rigorous verification algorithm. `value` and its special-function
and summation dependencies make up the substantive translation work.

Sage itself documents the general computation as not provably correct:
https://github.com/sagemath/sage/blob/develop/src/sage/lfunctions/lcalc.py

No claim is made that the new exact derivative search is a line-by-line
translation or behaviorally equivalent to that heuristic. Such equivalence would
not establish correctness of the analytic rank anyway. No upstream C++ code has
been copied into the Lean implementation.

## Why numerical precision alone does not suffice

A small enclosure containing zero does not prove exact vanishing. To establish
rank r, derivatives of orders below r must vanish exactly and the r-th derivative
must be nonzero. A rigorously separated interval can prove nonvanishing. Exact
vanishing needs identities or another rigorous argument. In particular, root
number parity only forces one parity of derivatives to vanish; it does not
settle all lower derivatives for high rank. No BSD assumption is made here.

The core represents a proved zero as a singleton-zero box; a backend must first
prove the identity allowing it to produce that box. All uncertainty is explicit.
There is no promise that a general rank computation terminates successfully.
Finite searches always terminate, but can return `none`.

## Implementation sequence

1. Define elliptic-curve L-series and normalization against mathlib objects.
2. Implement exact finite-field point counts, bad Euler factors, prime-power
   coefficient recurrences, and multiplicativity. Give each routine a separate
   theorem relating it to the mathematical coefficients.
3. Implement rational/dyadic interval arithmetic, exp, log, gamma/incomplete
   gamma as needed, with enclosures and termination proofs for each routine.
4. Prove an analytic evaluation formula, explicit truncation/tail bounds, and
   derivative bounds; implement its finite sums in Lean.
5. Supply exact vanishing proofs for the supported curve classes, beginning
   with rank 0 and functional-equation-forced rank 1 cases. Higher ranks need
   additional exact arguments; never convert a tolerance into equality.
6. Connect this backend to `computeRank`, generate a certificate naming the
   exact curve, normalization, output, and end-to-end theorem, then replay it.
7. Run the strict LMFDB regression suite. Require 100 matches, no unresolved
   cases, and 100 independently checked analytic certificates before claiming
   complete verified coverage. Database values remain external test oracles.

The current core has been proved. Stage 2 now has proved integral invariants,
good-prime point counts and traces, and a prime-power recurrence whose generating
series inverts the local Euler polynomial. Its bad-prime/minimal-model and global
coefficient-identification parts remain. Stage 3 now reuses Ledvinka's basic
dyadic interval infrastructure with a proved adapter; transcendental evaluation
and tail bounds remain. The continuation, analytic-rank, and remaining backend
stages are not complete. The 100-case fixture and strict reporting harness for
stage 7 are present. See [backend status](ELLIPTIC_BACKEND.md) and
[the TauCeti/interval audit](INFRASTRUCTURE.md) for exact capabilities and gaps.

## Trust and execution

The pure functions are ordinary Lean definitions with proofs. Compiled execution
erases proofs, so a binary's printed output alone is not a new kernel proof of
an execution trace. The generated `.lean` file supplies the stronger replayable
check: `decide` proves the concrete computation equation, and a proved theorem
connects it to analytic order. The checked demo certificate has no custom axioms;
its analytic theorem uses Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. The audit prints the actual dependencies, rather than hiding them.

The compiler, operating system, and I/O can affect availability or output, but
an incorrect generated result will not pass independent Lean replay. This does
not certify the authenticity of LMFDB data or unverified input ingestion.

## Explicit user-authorized modularity axiom

The default proof boundary above is unchanged. The optional
`VerifiedLcalc.Assumptions.Modularity` module now contains the single named
axiom `ellipticModularity`, authorized by the user on 2026-11-17. Its exact
statement, dependent certificates and separate audit are documented in
[ASSUMPTIONS.md](ASSUMPTIONS.md). Those results are conditional; they must not
be reported as axiom-free elliptic rank certificates. Numerical correctness,
BSD and cutoff-based exact vanishing have not been axiomatized.

## Integrated arithmetic and central analysis

`AuditIntegration.lean` guards the selected TauCeti local-factor and
multiplicativity theorems, our arithmetic adapter, the sum–integral exchange,
the Fourier-to-central formula, and the interval-to-rank-zero implication.
These implications accept the required mathematical witnesses as arguments
and depend only on standard foundational axioms. They do not establish that
the concrete prime-power compatibility input has been supplied. See
[INTEGRATION.md](INTEGRATION.md) for the exact remaining boundary.

The global prime-power extraction and actual coefficient bound are now proved
without custom axioms. `AssumedCurve11Central.analytic_rank_zero` supplies the
finite prefix and concludes exact order zero with no further proof arguments;
its only custom axiom is `ellipticModularity`. A separate regression soundness
theorem connects the opt-in conditional runtime cache to that continuation.
