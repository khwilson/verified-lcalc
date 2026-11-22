# Certificate contract modules

The canonical contract API is collected in `VerifiedLcalc.Certificates`. A
contract module declares mathematical data carried by a certificate; checking
algorithms, JSON encodings, and proofs that construct contracts stay in
`VerifiedLcalc.Certification`, `VerifiedLcalc.Certificate`, and `VerifiedLcalc.Tactic`.
The umbrella imports these data contracts without the checker modules that
construct or verify their evidence.

## Current module map

| Public type | Canonical module | Definition provenance |
| --- | --- | --- |
| `IntegralXSupport` | `VerifiedLcalc.Certificates.IntegralXSupport` | Mathlib's `WeierstrassCurve` and affine equation (`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic`). |
| `CompleteIntegralPointFacts` | `VerifiedLcalc.Certificates.IntegralPointCount` | The set of integral points is TauCeti's `WeierstrassCurve.integralPoints`; coordinate completeness and cardinality are certificate evidence. |
| `AlgebraicRankBounds` | `VerifiedLcalc.Certificates.AlgebraicRank` | Mathlib's `Module.finrank` on the rational affine point module; TauCeti supplies the Mordell–Weil finite-generation instance for nonsingular rational curves. |
| `RegulatorClaim`, `RegulatorFacts` | `VerifiedLcalc.Certificates.Regulator` | TauCeti's Néron–Tate regulator; the claim is raw decimal data and the facts carry a proved real enclosure. |
| `SpecialLValueClaim`, `SpecialLValueFacts` | `VerifiedLcalc.Certificates.SpecialValue` | The claim is exact reported data; facts state the normalized leading-coefficient enclosure for every `ArithmeticModularRealization` of the indexed curve. The realization contract is moving to this umbrella; the adapter keeps its compatibility import until that extraction lands. |
| `DegreeTwoIsogenyFact` | `VerifiedLcalc.Certificates.DegreeTwoIsogeny` | TauCeti's isogeny type, kernel, and degree (`Isogeny.Kernel` and `Isogeny.Degree`). Velu construction and minimum-degree checking remain in `VerifiedLcalc.Certification.DegreeTwoIsogeny`. |

`VerifiedLcalc.Certificate.IntegralXSupport` remains an import-only compatibility
module. `tests/consumers/CertificateContracts.lean` imports the plural umbrella
and rejects accidental imports of the corresponding local checker modules.
