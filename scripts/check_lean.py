"""Build Lean libraries and replay the mathematical regression and axiom audits."""

import argparse
import re
import shlex
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDITS = (
    "Audit.lean",
    "AuditArithmetic.lean",
    "AuditExtended.lean",
    "AuditTame.lean",
    "AuditWild.lean",
    "AuditGeneralModularity.lean",
    "AuditDerivative.lean",
    "AuditAssumptions.lean",
    "AuditLowRankBSD.lean",
    "AuditIntegration.lean",
    "AuditIntervalComponents.lean",
    "tests/VerifiedLcalcTests/Fixtures/Cubic.lean",
    "tests/consumers/Cubic.lean",
    "tests/consumers/TorsionBound.lean",
    "tests/consumers/DegreeTwoIsogeny.lean",
    "tests/consumers/IsogenyClass.lean",
    "tests/consumers/GaloisImage.lean",
    "tests/consumers/Geometry.lean",
    "tests/consumers/SecondMellinDerivative.lean",
    "tests/consumers/Additive.lean",
    "tests/consumers/Wild.lean",
    "tests/consumers/CertificateContracts.lean",
    "tests/consumers/WitnessLayout.lean",
    "tests/consumers/RawWitnessImports.lean",
    "tests/consumers/CertificateCompatibility.lean",
    "tests/consumers/TorsionFacts.lean",
    "tests/consumers/TorsionBoundCompatibility.lean",
    "tests/consumers/CurveWitnessCompatibility.lean",
    "tests/consumers/RawCertificateData.lean",
    "tests/OrderCheckGenerality.lean",
    "tests/CyclicTorsionStructure.lean",
    "tests/TwoFactorTorsion.lean",
)


def run(args: list[str]) -> None:
    print(shlex.join(args), flush=True)
    subprocess.run(args, cwd=ROOT, check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()
    if not args.skip_build:
        run(["lake", "build"])
        run(
            [
                "lake",
                "-f",
                "lakefile.certificates.lean",
                "build",
                "CertifiedCurves",
                "VerifiedLcalc.Certificates",
                "VerifiedLcalcTests",
                "VerifiedLcalc.Verification.Precision",
                "VerifiedLcalcTests.Fixtures.TwoFactorTorsion",
            ]
        )
        audit_modules = sorted(
            {
                module
                for source in AUDITS
                for module in re.findall(
                    r"^import (VerifiedLcalc[^\s]+)",
                    (ROOT / source).read_text(),
                    re.MULTILINE,
                )
            }
        )
        run(["lake", "build", *audit_modules])
    for source in (
        "tests/CertifyEC.lean",
        "tests/CertifyECSerialization.lean",
        "tests/CertifyECJson.lean",
        "tests/CertifyECData.lean",
        "tests/CertifyECPoints.lean",
        "tests/CertifyECInvariants.lean",
        "tests/CurveHypotheses.lean",
        "tests/FinitePointCount.lean",
        "tests/UpstreamCandidates.lean",
        "tests/MathlibReuse.lean",
        "tests/GlobalMinimality.lean",
        "tests/IntervalMultiplication.lean",
        "tests/OddPointCount.lean",
        "tests/OrderCheckGenerality.lean",
        "tests/consumers/CertifiedECConsumer.lean",
        "tests/consumers/CatalogueAnalyticRank.lean",
        "tests/consumers/CertifiedECDataConsumer.lean",
        "tests/consumers/CertifiedECPointsConsumer.lean",
        "tests/consumers/CertifiedECInvariantsConsumer.lean",
        "tests/consumers/TwoFactorTorsion.lean",
        "tests/consumers/MordellWeilRank.lean",
        "tests/consumers/LowRankBSD.lean",
        "tests/consumers/LowRankBSDDefaultAbsent.lean",
        "tests/consumers/CompleteIntegralPoints.lean",
        "tests/consumers/CertificateCompatibility.lean",
        "tests/consumers/SpecialLValue.lean",
        "tests/consumers/BSDFields.lean",
        "tests/consumers/ExtensionData.lean",
        "tests/consumers/SpecialValueContract.lean",
    ):
        run(["lake", "-f", "lakefile.certificates.lean", "env", "lean", source])
    for source in AUDITS:
        run(["lake", "env", "lean", source])
    print("All Lean checks passed.", flush=True)


if __name__ == "__main__":
    main()
