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
| `RegulatorClaim`, `RegulatorFacts` | `VerifiedLcalc.Certificates.Regulator` | TauCeti's Néron–Tate regulator; the claim is raw decimal data and the facts carry a proved real enclosure. |
| `DegreeTwoIsogenyFact` | `VerifiedLcalc.Certificates.DegreeTwoIsogeny` | TauCeti's isogeny type, kernel, and degree (`Isogeny.Kernel` and `Isogeny.Degree`). Velu construction and minimum-degree checking remain in `VerifiedLcalc.Certification.DegreeTwoIsogeny`. |
| `TorsionBoundWitness` | `VerifiedLcalc.Certificates.TorsionFacts` | Submitted prime/count data; the underlying finite-field object is Mathlib's `ZMod` and TauCeti's `WeierstrassCurve.pointCount`. |
| `TorsionDivisorFacts` | `VerifiedLcalc.Certificates.TorsionFacts` | Mathematical evidence states prime and odd hypotheses, ellipticity of both reductions, the actual point-count gcd, positivity, and divisibility of the full torsion subgroup cardinality. `VerifiedLcalc.Certification.TorsionBoundFacts` adapts the finite computation to these endpoints. |
| `CyclicTorsionFacts`, `TwoFactorTorsionFacts` | `VerifiedLcalc.Certificates.TorsionFacts` | Use Mathlib `ZMod`, additive equivalences, and the actual `AddCommGroup.torsion` subgroup of TauCeti's rational affine point group. |
| `TorsionPrimeSupportFacts`, `TorsionFacts` | `VerifiedLcalc.Certificates.TorsionFacts` | The support proposition refers directly to prime divisors of `Nat.card` of the actual full rational torsion subgroup. |
| `Box`, `RealInterval` | `VerifiedLcalc.Certificates.Enclosures` | Exact rational endpoints; `Box.valid`, `Box.isZero`, and `Box.excludesZero` state the interval predicates directly. |
| `PrecisionPolicy` | `VerifiedLcalc.Certificates.PrecisionPolicy` | Raw precision bit count and its exact legacy cutoff; the cutoff is a classification threshold, not an evaluator error bound. |
| `MinimalityWitness`, `TateWitness`, `WildData` | `VerifiedLcalc.Certificates.Transcripts` | Finite arithmetic transcript data. Rechecking and geometric/local compatibility remain in the reduction and Tate cores. |
| `CentralResult`, `DerivativeResult` | `VerifiedLcalc.Certificates.NumericalData` | Raw numerical outputs, including equation, normalization inputs, coefficient prefix, precision, integral/quadrature enclosure and tail. |
| `CentralPayloadCorrect`, `DerivativePayloadCorrect` | `VerifiedLcalc.Certificates.NumericalContracts` | Exact predicates relating payloads to the specified central and first-derivative formulae. Evaluators and their correctness proofs remain in the existing implementation modules. |
| `DiscriminantWitness`, `EllipticProofs` | `VerifiedLcalc.Certificates.CurveWitness` | Use Mathlib's `WeierstrassCurve` discriminant and invariant expressions, with equality proofs indexed by the supplied equation. |
| `AbcQualityClaim` | `VerifiedLcalc.Certificates.CurveWitness` | Raw submitted rational report, error, and factor list; no checking algorithm is part of the record. |
| `RationalInvariantFacts` | `VerifiedLcalc.Certificates.RationalInvariants` | Sign, rational j-invariant, and integer-localization predicate are stated directly for the integral equation or its rational base change. |
| `AbcQualityFacts` | `VerifiedLcalc.Certificates.RationalInvariants` | Refers to TauCeti's `WeierstrassCurve.abcQuality`, exact reduced abc-product factorization, and prime factors. The checker-success boolean remains in the `Certification.CheckedAbcQualityFacts` backend companion because the exact error enclosure does not imply the backend's particular interval test succeeded. |
| `AffineMembership`, `InfiniteOrderPointFact`, `IndependentPointFacts` | `VerifiedLcalc.Certificates.PointFacts` | Membership is the actual affine Weierstrass equation; rational points lift through TauCeti's `pointOfIntegralSolution`; infinite order and integer linear independence refer to those points. |
| `TorsionGeneratorOrderFacts` | `VerifiedLcalc.Certificates.PointFacts` | Exact additive orders of the submitted points, indexed by Mathlib's `addOrderOf`. |
| `GeneratorCountFacts` | `VerifiedLcalc.Certificates.PointFacts` | The claimed count equals the length of the supplied coordinate list; it makes no generation claim. |
| `IntegralYFiberFacts` | `VerifiedLcalc.Certificates.PointFacts` | Each finite fiber is exactly the set of integer y-coordinates satisfying the supplied Weierstrass equation at its indexed x-coordinate. |

`VerifiedLcalc.Certificate.IntegralXSupport` remains an import-only compatibility
module. Existing singular import paths continue to expose migrated records for
compatibility. `tests/consumers/CertificateContracts.lean` imports the plural
umbrella, checks these public declarations, and rejects accidental imports of
the corresponding checker and evaluator modules.
`VerifiedLcalc.Certificate.EllipticWitness` reexports the moved curve witness
declarations for existing import paths.
