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
| `DegreeTwoIsogenyFact` | `VerifiedLcalc.Certificates.DegreeTwoIsogeny` | TauCeti's isogeny type, kernel, and degree (`Isogeny.Kernel` and `Isogeny.Degree`). Velu construction and minimum-degree checking remain in `VerifiedLcalc.Certification.DegreeTwoIsogeny`. |
| `TorsionBoundWitness` | `VerifiedLcalc.Certificates.TorsionFacts` | Submitted prime/count data; the underlying finite-field object is Mathlib's `ZMod` and TauCeti's `WeierstrassCurve.pointCount`. |
| `TorsionDivisorFacts` | `VerifiedLcalc.Certificates.TorsionFacts` | Mathematical evidence states prime and odd hypotheses, ellipticity of both reductions, the actual point-count gcd, positivity, and divisibility of the full torsion subgroup cardinality. `VerifiedLcalc.Certification.TorsionBoundFacts` adapts the finite computation to these endpoints. |
| `CyclicTorsionFacts`, `TwoFactorTorsionFacts` | `VerifiedLcalc.Certificates.TorsionFacts` | Use Mathlib `ZMod`, additive equivalences, and the actual `AddCommGroup.torsion` subgroup of TauCeti's rational affine point group. |
| `TorsionPrimeSupportFacts`, `TorsionFacts` | `VerifiedLcalc.Certificates.TorsionFacts` | The support proposition refers directly to prime divisors of `Nat.card` of the actual full rational torsion subgroup. |

`VerifiedLcalc.Certificate.IntegralXSupport` remains an import-only compatibility
module. `tests/consumers/CertificateContracts.lean` imports the plural umbrella
and rejects accidental imports of the corresponding local checker modules.
