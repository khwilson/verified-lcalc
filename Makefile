.PHONY: check format test certificates test-certificates

check:
	uv run --locked ruff check .
	uv run --locked ruff format --check .
	uv run --locked ty check --error-on-warning

format:
	uv run --locked ruff check --fix .
	uv run --locked ruff format .

test:
	uv run --locked pytest

certificates:
	lake -f lakefile.certificates.lean build CertifiedCurves

test-certificates: certificates
	lake -f lakefile.certificates.lean env lean tests/CertifyEC.lean
	lake -f lakefile.certificates.lean env lean tests/CertifyECJson.lean
	lake -f lakefile.certificates.lean build VerifiedLcalcTests VerifiedLcalc.Certification.Precision VerifiedLcalc.UpstreamCandidates.TauCeti.PointCount
	lake -f lakefile.certificates.lean env lean tests/CurveHypotheses.lean
	lake -f lakefile.certificates.lean env lean tests/FinitePointCount.lean
	lake -f lakefile.certificates.lean env lean tests/UpstreamCandidates.lean
	lake -f lakefile.certificates.lean env lean tests/MathlibReuse.lean
	lake -f lakefile.certificates.lean env lean tests/consumers/CertifiedECConsumer.lean

.PHONY: test-lean
test-lean:
	uv run --locked python scripts/check_lean.py
