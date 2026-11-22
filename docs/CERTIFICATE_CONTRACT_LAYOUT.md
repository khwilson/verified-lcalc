# Certificate contract modules

The canonical contract API is collected in `VerifiedLcalc.Certificates`. A
contract module declares mathematical data carried by a certificate; checking
algorithms, JSON encodings, and proofs that construct contracts stay in
`VerifiedLcalc.Certification`, `VerifiedLcalc.Certificate`, and `VerifiedLcalc.Tactic`.
The umbrella imports only contract modules.

## Current module map

| Public type | Canonical module | Definition provenance |
| --- | --- | --- |
| `IntegralXSupport` | `VerifiedLcalc.Certificates.IntegralXSupport` | Mathlib's `WeierstrassCurve` and affine equation (`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic`). |
| `CompleteIntegralPointFacts` | `VerifiedLcalc.Certificates.IntegralPointCount` | The set of integral points is TauCeti's `WeierstrassCurve.integralPoints`; coordinate completeness and cardinality are certificate evidence. |
| `AlgebraicRankBounds` | `VerifiedLcalc.Certificates.AlgebraicRank` | Mathlib's `Module.finrank` on the rational affine point module; TauCeti supplies the Mordell–Weil finite-generation instance for nonsingular rational curves. |
| `DegreeTwoIsogenyFact` | `VerifiedLcalc.Certificates.DegreeTwoIsogeny` | TauCeti's isogeny type, kernel, and degree (`Isogeny.Kernel` and `Isogeny.Degree`). Velu construction and minimum-degree checking remain in `VerifiedLcalc.Certification.DegreeTwoIsogeny`. |
| `Box`, `RealInterval` | `VerifiedLcalc.Certificates.Enclosures` | Exact rational endpoints; `Box.valid`, `Box.isZero`, and `Box.excludesZero` state the interval predicates directly. |
| `PrecisionPolicy` | `VerifiedLcalc.Certificates.PrecisionPolicy` | Raw precision bit count and its exact legacy cutoff; the cutoff is a classification threshold, not an evaluator error bound. |
| `MinimalityWitness`, `TateWitness`, `WildData` | `VerifiedLcalc.Certificates.Transcripts` | Finite arithmetic transcript data. Rechecking and geometric/local compatibility remain in the reduction and Tate cores. |
| `CentralResult`, `DerivativeResult` | `VerifiedLcalc.Certificates.NumericalData` | Raw numerical outputs, including equation, normalization inputs, coefficient prefix, precision, integral/quadrature enclosure and tail. |
| `CentralPayloadCorrect`, `DerivativePayloadCorrect` | `VerifiedLcalc.Certificates.NumericalContracts` | Exact predicates relating payloads to the specified central and first-derivative formulae. Evaluators and their correctness proofs remain in the existing implementation modules. |

`VerifiedLcalc.Certificate.IntegralXSupport` remains an import-only compatibility
module. Existing singular import paths continue to expose migrated records for
compatibility. `tests/consumers/CertificateContracts.lean` imports the plural
umbrella, checks these public declarations, and rejects accidental imports of
the corresponding checker and evaluator modules.
