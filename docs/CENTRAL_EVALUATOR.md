# Central exponential-series evaluator

The executable `ec-central` computes a finite central expression from an integral
Weierstrass equation, supplied conductor N, supplied sign w, term limit M and the
global precision policy. It implements the numerical side of the split-Mellin
formula

    L(E,1) = (1+w) * sum_{n>=1} (a_n/n) * exp(-2*pi*n/sqrt(N)).

`Assumptions/CentralSeries.lean` now derives this identity for a supplied modular
realization and proved coefficient bound, using mathlib's Fourier/Mellin
identities and a proved sum–integral exchange. `CentralEvaluator.lean` connects
it to the interval evaluator once actual-curve prime-power identification is
supplied. The actual global bound is now proved. A finite-prefix interface suffices,
and the conditional 11.a2 certificate supplies it with no remaining proof
arguments. General CLI outputs still require that identification, so they
remain labelled `model-central-expression`.

## Implemented mathematical components

- `CoefficientCore.lean` computes repeated-division prime exponents and a finite
  prime-factor table, sharing point counts across the coefficient prefix.
  At smooth primes it uses `(trace,p)`; at singular primes it uses `(trace,0)`,
  where the trace counts all equation solutions plus infinity.
- `Coefficients.lean` proves that computed prime exponents equal
  `Nat.factorization`, and that each coefficient is the product of the
  corresponding prime-power recurrence coefficients. The prefix includes mixed
  products and powers, not only prime coefficients.
- `Bounds.lean` relates the finite table to the canonical factorization product
  and proves the weak bound `|a_n| <= n^3` for the model Euler factors, using
  elementary point counting and recurrence estimates. Identifying these with
  the actual curve coefficients remains a separate arithmetic obligation.
- `RationalExp.lean` proves outward exponential bounds for real arguments between
  rational endpoints, including irrational arguments. Negative coefficients
  reverse the endpoints. It proves composition under finite addition.
- `CentralFinite.lean` proves the bounds for the actual quantity
  `alpha = 2*pi/sqrt(N)`. It uses integer square-root bounds and mathlib's proved
  20-decimal bounds for pi. The fixed pi interval limits attainable accuracy;
  increasing precision does not silently erase that error. It then proves the
  finite central-expression enclosure.
- `CentralTail.lean` proves a geometric majorant and a truncation-error theorem.
  With `q >= exp(-alpha)`, a bound `|a_n/n| <= n^2` gives, past M,

      rho = q * ((M+2)/(M+1))^2
      remainder <= (M+1)^2 * q^(M+1) / (1-rho).

  The evaluator requires `q >= 0` and `rho < 1` and otherwise returns `none`.
  It multiplies this remainder by `|1+w|`. It computes q by an outward
  exponential enclosure at the lower alpha endpoint; there is no floating-point
  arithmetic or tolerance-based truncation.
- `Central.lean` combines the finite and tail proofs. `evaluateCentral_correct`
  proves the complete finite payload contract.
  `evaluateCentral_sound` proves containment when supplied with a
  `CentralSeriesEvidence` object for the actual value.

That evidence must prove a genuine convergent exponential-series identity, the
prefix identity with the computed coefficients, and the global majorant. These
are explicit proof arguments, not flags. The caller cannot use the divergent
raw coefficient Dirichlet series at s=1 as this identity.

## Usage and saved output

```
lake build
lake exe ec-central 11.a2 1 32
lake exe ec-central --all 1 32
lake exe ec-central 11.a2 1 8 VerifiedLcalc/Certificates/Curve11Central.lean
lake build VerifiedLcalc.Certificates.Curve11Central
lake env lean VerifiedLcalc/Certificates/Curve11Central.lean
lake env lean certificates/Curve11Central.lean
```

The optional output file contains a complete literal `CentralResult`, including
the equation, supplied conductor and sign, coefficient prefix, precision policy,
alpha interval, geometric upper bound, tail and final rectangle. Kernel replay
checks the finite data and invokes the universal enclosure theorem. The theorem
still takes `CentralSeriesEvidence` as an explicit argument; it does not assert
that the curve's L-function has been certified. The example uses eight terms to
keep the replay small. These checks recompute small coefficient and exponential
enclosure quantities, but do not call the complete producer or an analytic
continuation algorithm. More efficient per-operation witnesses remain future
work if replay costs warrant them.

An unchanged output is not rewritten. Lake caches the compiled saved theorem;
an import-only consumer reuses it. The payload is not yet wired into a remote
cache or a canonical request-digest store. Dependency provenance is supplied by
the pinned project and imported Lean modules, not authenticated by metadata.

On 2026-11-17, the 53-bit, 32-term run for 11.a2 with supplied sign +1 produced
an interval approximately `[0.2538418608559099, 0.2538418608559115]`, with a
tail allowance about `1.83e-24`. The bulk run produced finite payloads for all
100 fixture inputs with sign **supplied as +1 for every input**. This tests the
evaluator and does not verify their root numbers, central values or ranks.

## Conditional analytic connection

The opt-in temporary modularity package now includes general semistable
conductor and sign compatibility. `Assumptions/CentralIntegral.lean` proves the
split-Mellin central integral from a supplied modular realization; it does not
assume the numerical formula. It gives exact central vanishing for negative
sign. The saved conditional 37.a1 certificate therefore proves analytic rank
at least one. Termwise integration and the numerical enclosure connection are now proved
with an explicit arithmetic prime-power compatibility input. The new actual global coefficient bound removes that infinite arithmetic
input: only finite prefix identification remains. The separate conditional
11.a2 rank-zero certificate supplies it completely.
See [ASSUMPTIONS.md](ASSUMPTIONS.md) for the precise trusted boundary.

## Remaining elliptic and derivative proofs

The supplied model must be proved minimal where required, including the
classification of its bad local factors. The global coefficient identification,
conductor, root number, entire continuation and split-Mellin formula must be
connected to the actual elliptic curve. The standard coefficient majorant also
needs its proof from those mathematical coefficients. None of these are inferred
from matching the LMFDB label or expected rank.

Only the central value is implemented. For numerical rank >= 4 we still need
the derivative kernels and their certified tails for orders 1 through 3. A
small central value alone cannot fill these entries. Exact vanishing and the
numerical policy remain separate, as explained in [NUMERICAL_RANK.md](NUMERICAL_RANK.md).
The default elliptic subject interpretation remains unsupported. The opt-in
conditional interface now has an exact rank-zero certificate for 11.a2;
general curve/derivative coverage remains unfinished.

## Validation recorded on 2026-11-17

The full build passed. Fresh source replay of the saved 11.a2 payload and the
existing cubic certificate passed, as did both compiled-theorem consumers and
the axiom audit. The audit found only standard Lean/mathlib foundational axioms,
with no `sorryAx` or native-reduction verification axiom. Invalid root number 0
was rejected; supplied root number -1 produced the zero central expression.
The strict LMFDB rank gate still exited 1 with 100 inconclusive curves.

The new [integration status](INTEGRATION.md) separates the completed general
analytic pipeline from the remaining concrete arithmetic identifications.
