# Certificate witnesses

Import `VerifiedLcalc.Certificate.Witnesses` for the public structures used by
`certify_ec`. The [witness directory](../VerifiedLcalc/Certificate/Witnesses)
contains their Lean declarations.

| Start here | What to read |
| --- | --- |
| [EllipticWitness.lean](../VerifiedLcalc/Certificate/Witnesses/EllipticWitness.lean) | `EllipticWitness` holds the integral Weierstrass equation and the optional input for each check. `IntegralCurveProofs` carries additional input proofs. |
| [EllipticCertificate.lean](../VerifiedLcalc/Certificate/Witnesses/EllipticCertificate.lean) | `EllipticCertificate` is the type of `Name.certificate`. Its fields group the checked equation, rational invariants, algebraic, arithmetic and analytic facts, torsion, and isogeny evidence for the indexed curve. |
| [CurveProofs.lean](../VerifiedLcalc/Certificate/Witnesses/CurveProofs.lean) | `DiscriminantWitness` pairs a Mathlib curve with a value and the proof `curve.Δ = discriminant`. `EllipticProofs` stores optional checked invariants indexed by one equation. |

## Field structures

| Subject | Witness files and mathematical content |
| --- | --- |
| Rational invariants | [RationalInvariants](../VerifiedLcalc/Certificate/Witnesses/RationalInvariants.lean) records the sign, rational j-invariant, and an enclosure for TauCeti's abc quality with its factorization evidence. |
| Rational and integral points | [PointMembership](../VerifiedLcalc/Certificate/Witnesses/PointMembership.lean) states the affine equation. [PointFacts](../VerifiedLcalc/Certificate/Witnesses/PointFacts.lean) records exact orders, linear independence, generator-list length, and integral y-fibers. [IntegralPoints](../VerifiedLcalc/Certificate/Witnesses/IntegralPoints.lean) covers exhaustive x-coordinate support and the cardinality of TauCeti's set of integral points. |
| Mordell–Weil rank and regulator | [AlgebraicRank](../VerifiedLcalc/Certificate/Witnesses/AlgebraicRank.lean) gives bounds on Mathlib's integer `Module.finrank` using TauCeti's Mordell–Weil finite-generation instance. [Regulator](../VerifiedLcalc/Certificate/Witnesses/Regulator.lean) states an enclosure for TauCeti's Néron–Tate regulator. |
| Torsion and isogenies | [Torsion](../VerifiedLcalc/Certificate/Witnesses/Torsion.lean) covers reduction point counts, divisibility, the full torsion subgroup and its invariant factors. [DegreeTwoIsogeny](../VerifiedLcalc/Certificate/Witnesses/DegreeTwoIsogeny.lean) uses TauCeti's isogeny, kernel and degree. |
| Reduction and arithmetic | [LocalClaims](../VerifiedLcalc/Certificate/Witnesses/LocalClaims.lean) contains supplied local rows and isogeny edge claims. [Transcripts](../VerifiedLcalc/Certificate/Witnesses/Transcripts.lean) contains minimality and tame/wild Tate data. [ArithmeticFacts](../VerifiedLcalc/Certificate/Witnesses/ArithmeticFacts.lean) includes minimal-model facts, local Tamagawa and Kodaira evidence, coefficients and conditional modular level and sign. |
| L-function and leading coefficient | [AnalyticFacts](../VerifiedLcalc/Certificate/Witnesses/AnalyticFacts.lean) contains verified payloads, enclosures and analytic rank for an explicit realization. [SpecialValue](../VerifiedLcalc/Certificate/Witnesses/SpecialValue.lean) states the reported Taylor leading coefficient and its error bound for that curve. |

The directory also contains the derivative boxes, numerical outputs, precision
claims, and generic scan and artifact records. [Witnesses.lean](../VerifiedLcalc/Certificate/Witnesses.lean)
lists the ordinary modules. [AssumedEvidence](../VerifiedLcalc/Certificate/Witnesses/AssumedEvidence.lean)
and [CurvePrecision](../VerifiedLcalc/Certificate/Witnesses/CurvePrecision.lean)
have separate imports because their types refer to the modularity assumption.

## Predicates, computations and theorems

A witness field may ask for a proof of a proposition. Give the proof where the
witness is constructed. Put named predicates, derived instances, constructors
implemented as functions, verification code, and theorems outside the witness
directory. For example, the [torsion checker](../VerifiedLcalc/Certification/TorsionBoundFacts.lean)
constructs evidence about the actual rational torsion subgroup, and the
[special-value checker](../VerifiedLcalc/Certification/SpecialValue.lean)
turns derivative enclosures into an error bound for the reported coefficient.

The earlier `VerifiedLcalc.Certificates` and singular import paths continue to
provide their public APIs. The [layout audit](../tests/consumers/WitnessLayout.lean)
parses every witness file with Lean and checks where the main types are defined.
The [import audit](../tests/consumers/CertificateContracts.lean) exercises the
lightweight compatibility API, and the [projection tests](../tests/consumers/CertificateCompatibility.lean)
check existing downstream proofs.
