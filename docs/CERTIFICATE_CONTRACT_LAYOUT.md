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
| `Witness`, `Certificate` | `VerifiedLcalc.Certificates.Scan` | A typed finite proof that earlier boxes are singleton zero and the selected box excludes zero. The executable scan remains in the legacy module. |
| `Box.Contains`, `Encloses` | `VerifiedLcalc.Certificates.AnalyticEnclosures` | Exact real and imaginary interval membership for supplied complex values; analytic derivative enclosures remain proof obligations. |
| `AnalyticCertificate` | `VerifiedLcalc.Certificates.AnalyticRank` | A witnessed rank tied to the same derivative boxes and the analytic order theorem. |
| `Artifacts.{Normalization,Subject,Settings,BuildIdentity,Request,Artifact,WitnessAccepts,Checked}` | `VerifiedLcalc.Certificates.Artifacts` | Raw request and artifact data plus a pure witness-based acceptance contract. Search and Boolean checking remain in the singular compatibility module. |
| `NumericalRanks.{Request,Artifact,CutoffAccepts,Checked}` | `VerifiedLcalc.Certificates.NumericalRanks` | Raw threshold-observation data and its exact rational cutoff contract. |
| `Artifacts.{Subject.Denotes,AnalyticEvidence}`, `NumericalRanks.{SmallDerivatives,Evidence,ExactVanishingHypothesis}` | `VerifiedLcalc.Certificates.AnalyticEvidence` | Mathematical function, derivative-enclosure, and conditional exact-vanishing obligations, independent of the evaluator. |

Existing singular import paths continue to expose migrated records and
historical `.computed`/`.accepted` projections for compatibility.
`tests/consumers/CertificateContracts.lean` imports the plural umbrella, checks
the public declarations, and rejects accidental imports of checker and
evaluator modules. `tests/consumers/CertificateCompatibility.lean` checks the
legacy projections through the singular imports.
