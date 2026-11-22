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

`VerifiedLcalc.Certificate.IntegralXSupport` remains an import-only compatibility
module. `tests/consumers/CertificateContracts.lean` imports the plural umbrella
and rejects accidental imports of the corresponding local checker modules.
