# Certificate witnesses

Import `VerifiedLcalc.Certificate.Witnesses` for the public structures used by
`certify_ec`. The command entry point is
`VerifiedLcalc.Tactic.CertifyEC`. The [witness directory](../VerifiedLcalc/Certificate/Witnesses)
contains their Lean declarations.

| Start here | What to read |
| --- | --- |
| [EllipticWitness.lean](../VerifiedLcalc/Certificate/Witnesses/EllipticWitness.lean) | `EllipticWitness` holds the integral Weierstrass equation and the optional input for each check. |
| [EllipticCertificate.lean](../VerifiedLcalc/Certificate/Witnesses/EllipticCertificate.lean) | `EllipticCertificate` is the type of `Name.certificate`. This file also defines `IntegralCurveProofs` for supplied proofs that span subjects. |
| [Invariants.lean](../VerifiedLcalc/Certificate/Witnesses/Invariants.lean) | `DiscriminantWitness` and `EllipticProofs`, together with exact rational-invariant claims. |

## Field structures

| Subject | Witness files and mathematical content |
| --- | --- |
| Rational invariants | [InputData.lean](../VerifiedLcalc/Certificate/Witnesses/InputData.lean) defines the reported `AbcQualityClaim`; [Invariants.lean](../VerifiedLcalc/Certificate/Witnesses/Invariants.lean) records the sign, rational j-invariant, and checked abc-quality evidence. |
| Rational and integral points | [Algebraic.lean](../VerifiedLcalc/Certificate/Witnesses/Algebraic.lean) records point membership, exact orders, linear independence, generator-list length, integral y-fibers, and exhaustive integral-point support. |
| Mordell–Weil rank and regulator | [Algebraic.lean](../VerifiedLcalc/Certificate/Witnesses/Algebraic.lean) gives bounds on Mathlib's integer `Module.finrank` and states an enclosure for TauCeti's Néron–Tate regulator. |
| Torsion and isogenies | [Algebraic.lean](../VerifiedLcalc/Certificate/Witnesses/Algebraic.lean) covers rational torsion orders, divisibility, the full torsion subgroup, invariant factors, and degree-two isogeny data. |
| Reduction and arithmetic | Raw local rows live in [InputData.lean](../VerifiedLcalc/Certificate/Witnesses/InputData.lean); [FinitePrimes.lean](../VerifiedLcalc/Certificate/Witnesses/FinitePrimes.lean) contains their checked local, minimal-model, Tamagawa, Kodaira, and coefficient facts. Conditional conductor and root-number facts are in [Invariants.lean](../VerifiedLcalc/Certificate/Witnesses/Invariants.lean). |
| L-function and leading coefficient | [Analytic.lean](../VerifiedLcalc/Certificate/Witnesses/Analytic.lean) contains verified payloads, enclosures, analytic rank, and leading-coefficient evidence for an explicit realization. |

The directory is organized by subject: `FinitePrimes`, `Analytic`, `Algebraic`,
and `Invariants`. The [InputData](../VerifiedLcalc/Certificate/Witnesses/InputData.lean)
module is the shared foundation for supplied fields, and
[ArtifactData](../VerifiedLcalc/Certificate/Witnesses/ArtifactData.lean) contains
the generic request/artifact payloads used by analytic evidence. Meanwhile,
[EllipticWitness](../VerifiedLcalc/Certificate/Witnesses/EllipticWitness.lean)
and [EllipticCertificate](../VerifiedLcalc/Certificate/Witnesses/EllipticCertificate.lean)
are the input and checked-output aggregates. The
[Witnesses.lean](../VerifiedLcalc/Certificate/Witnesses.lean) umbrella re-exports
the ordinary structures and excludes assumptions. Import
[Assumptions](../VerifiedLcalc/Certificate/Witnesses/Assumptions.lean) for
assumption-dependent evidence and precision claims.

## Module layout and migration

The former `VerifiedLcalc.Certificates.*` modules now live under
`VerifiedLcalc.Certificate.*`, grouped by purpose:

| Previous module | Current module |
| --- | --- |
| `Certificates.Artifacts`, `.ArtifactContracts`, `.ArtifactPrimitives` | `Certificate.Artifacts.Data`, `.Contracts`, `.Primitives` |
| `Certificates.Scan`, `.ScanPredicate` | `Certificate.Witnesses.Analytic` (certificate), `Certificate.Artifacts.ScanWitness` (predicate) |
| `Certificates.AnalyticEnclosures`, `.AnalyticEvidencePredicates` | `Certificate.Analytic.Enclosures`, `.EvidencePredicates` |
| `Certificates.AnalyticEvidence`, `.AnalyticRank` | `Certificate.Witnesses.Analytic` |
| `Certificates.Enclosures`, `.NumericalData`, `.NumericalContracts` | `Certificate.Numerical.Intervals`, `.Outputs`, `.Payloads` |
| `Certificates.NumericalRanks`, `.NumericalRankContracts`, `.PrecisionPolicy` | `Certificate.Numerical.RankData`, `.RankContracts`, `.Precision` (with records in `Witnesses.InputData`/`Witnesses.Analytic`) |
| `Certificates.AlgebraicRank`, `.CurveWitness`, `.DegreeTwoIsogeny` | `Certificate.Support.AlgebraicRank`, `Certificate.Support.CurveProofs`, `Certificate.Support.Isogenies` |
| `Certificates.IntegralPointCount`, `.IntegralXSupport` | `Certificate.Witnesses.Algebraic`, `Certificate.Witnesses.InputData` |
| `Certificates.PointFacts`, `.RationalInvariants`, `.Regulator` | `Certificate.Support.Points`, `Certificate.Witnesses.Invariants`, `Certificate.Support.Regulator` |
| `Certificates.SpecialValue`, `.TorsionFacts`, `.Transcripts`, `.WeierstrassInstances` | `Certificate.Support.SpecialValue`, `Certificate.Support.Torsion`, `Certificate.Support.Transcripts`, `Certificate.Support.WeierstrassInstances` |

Backend files formerly in `VerifiedLcalc.Certification/` are now in
`VerifiedLcalc.Verification/`; their declarations remain in the
`VerifiedLcalc.Certification` namespace. `VerifiedLcalc.Certificates` remains as
a single-file compatibility umbrella. There is no `Certificates/` or
`Certification/` source directory. `VerifiedLcalc.Certificate.Witnesses` and
`VerifiedLcalc.Tactic.CertifyEC` are the canonical data and command entrypoints.

## Which definitions the checked fields need

The raw `EllipticWitness` uses Mathlib and other witness records. The
checked `EllipticCertificate` also uses TauCeti's integral points,
regulator, reduction symbols and Tamagawa numbers. For example, a checked
local reduction row identifies its signed trace with TauCeti's
`(e.baseChange (ZMod p)).frobeniusTrace`. Its checker proves the equality
from the integer computation.

Some checked fields refer to project definitions. For example, a conditional
analytic rank quantifies over a modular realization with coefficient, conductor and
root-number compatibility. Central-value and derivative payloads record the
exact coefficient list, interval computations and error bounds that the
verifier checked. Their field types name those definitions so clients can
recover the full statements. See the [arithmetic realization](../VerifiedLcalc/EllipticCurve/Modularity/ArithmeticRealizationData.lean),
[finite payloads](../VerifiedLcalc/Certificate/Numerical/Payloads.lean)
and [TauCeti roadmap](TAUCETI_ROADMAP.md).

## Predicates, computations and theorems

A witness field may ask for a proof of a proposition. Give the proof where the
witness is constructed. Put named predicates, derived instances, constructors
implemented as functions, verification code, and theorems outside the witness
directory. For example, the [torsion checker](../VerifiedLcalc/Verification/TorsionBoundFacts.lean)
constructs evidence about the actual rational torsion subgroup, and the
[special-value checker](../VerifiedLcalc/Verification/SpecialValue.lean)
turns derivative enclosures into an error bound for the reported coefficient.

The `VerifiedLcalc.Certificates` umbrella remains available for existing
consumers. The [layout audit](../tests/consumers/WitnessLayout.lean)
parses every witness file with Lean and checks where the main types are defined.
The [import audit](../tests/consumers/CertificateContracts.lean) exercises the
lightweight compatibility API, and the [projection tests](../tests/consumers/CertificateCompatibility.lean)
check existing downstream proofs.
