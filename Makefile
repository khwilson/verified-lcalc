.PHONY: check format test certificates test-certificates

check:
	uv run --locked ruff check .
	uv run --locked ruff format --check .
	uv run --locked ty check --error-on-warning
	uv run --locked python scripts/build_lmfdb_dependency_roadmap.py

format:
	uv run --locked ruff check --fix .
	uv run --locked ruff format .

test:
	uv run --locked pytest

certificates:
	lake -f lakefile.certificates.lean build CertifiedCurves

test-certificates: certificates
	lake -f lakefile.certificates.lean env lean tests/CertifyEC.lean
	lake -f lakefile.certificates.lean env lean tests/CertifyECSerialization.lean
	lake -f lakefile.certificates.lean env lean tests/CertifyECJson.lean
	lake -f lakefile.certificates.lean env lean tests/CertifyECData.lean
	lake -f lakefile.certificates.lean env lean tests/CertifyECInvariants.lean
	lake -f lakefile.certificates.lean build VerifiedLcalcTests VerifiedLcalc.Verification.Precision VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount \
		VerifiedLcalc.Certificate.SerreInvariants
	lake -f lakefile.certificates.lean env lean tests/CertifyECPoints.lean
	lake -f lakefile.certificates.lean env lean tests/CurveHypotheses.lean
	lake -f lakefile.certificates.lean env lean tests/FinitePointCount.lean
	lake -f lakefile.certificates.lean env lean tests/UpstreamCandidates.lean
	lake -f lakefile.certificates.lean env lean tests/MathlibReuse.lean
	lake -f lakefile.certificates.lean env lean tests/GlobalMinimality.lean
	lake -f lakefile.certificates.lean env lean tests/IntervalMultiplication.lean
	lake -f lakefile.certificates.lean env lean tests/OddPointCount.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/CertifiedECConsumer.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/CertifiedECDataConsumer.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/CertifiedECPointsConsumer.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/CertifiedECInvariantsConsumer.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/GaloisImage.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/SerreInvariants.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/SpecialLValue.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/BSDFields.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/Geometry.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/PeriodGeometry.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/IntrinsicTorsionFaltingsIndex.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/ModularParametrization.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/Iwasawa.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/ExtensionData.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/SpecialValueContract.lean

.PHONY: test-lean
test-lean:
	uv run --locked python scripts/check_lean.py

.PHONY: test-lmfdb-ci
test-lmfdb-ci:
	lake -f lakefile.certificates.lean build CertifiedCurves.Json VerifiedLcalcTests.Fixtures.LmfdbCI
	lake -f lakefile.certificates.lean env lean tests/consumers/LmfdbCI.lean
	python3 scripts/check_fixture_coverage.py
	python3 scripts/check_lmfdb_dependency_contracts.py
	python3 scripts/check_lmfdb_producer_example.py
	VERIFIED_LCALC_PRODUCER_LEAN=1 python3 tests/test_produce_ec_witness.py
