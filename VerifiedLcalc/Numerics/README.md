# Numerical support used by elliptic certification

Every Lean module remaining here is reached by the elliptic certificate checker.

| Modules | Purpose |
| --- | --- |
| `RationalExpCore`, `RationalExp` | Outward-rounded exponential bounds, signed weighted sums, and their correctness proofs. They use the pinned Ledvinka implementation directly. |
| `RealIntervalCore`, `RealInterval` | Rational interval operations, checked log-series bounds, and their real interpretation. |
| `MellinSplit`, `ExponentialIntegral` | Functional-equation splitting, integration of exponential terms, and justified termwise integration. |
| `PolynomialTail` | Explicit polynomial/geometric remainder bounds. |
| `FourierInterval` | Fourier truncation and pointwise bounds for derivative quadrature cells. |
| `DerivativeTail`, `DerivativeQuadrature` | First-derivative tail estimates and the soundness of checked quadrature. |

The older `Dyadic`, `Exponential`, and `ExpSum*` prototype modules were retired.
Their box and exact-dyadic-sum adapters are not needed by the rational-interval
backend. Useful `dyadic_interval` regression examples are in
`tests/VerifiedLcalcTests/Arithmetic/Numerics.lean`; they are not imported by the checker.
General integration and analytic-order results are candidates for Mathlib;
modular quantitative estimates are candidates for TauCeti, as recorded in the
roadmap documents. No gamma evaluator or higher-derivative evaluator is claimed.
