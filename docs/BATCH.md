# Retired batch workflow

This workflow and its generated certificate corpus were retired on 2026-11-19.
Use [`certify_ec`](CERTIFY_EC.md) for checked, importable per-curve theorems.
The commands and paths below are historical documentation, not supported setup
instructions. Their implementation is preserved in baseline commit `fcdc4f2`.
The generic mathematical certifiers remain available.

## Historical workflow

Run the complete producer, kernel checker, certificate-cache update and strict
regression with:

    lake exe certify-batch

The mathematical code, candidate search, source producer and workflow runner
are Lean. The runner invokes Lake and the system checksum utility, records
statuses/hashes and assembles the proved registry. File/process orchestration
is outside the mathematical proof boundary; every generated mathematical
assertion and registry entry is checked by Lean. The fixture's expected ranks
are not passed to the producer or certificate checker.

## Checks and adaptation

`ec-batch` examines all exact curve inputs. The current route supports models
satisfying the semistable criterion `gcd(discriminant,c4)=1`. It uses the supplied
conductor only as a candidate: each generated certificate kernel-checks equality
with the arithmetic semistable conductor from the existing modularity package.
It likewise checks the computed arithmetic sign rather than trusting a sign
hint. The modularity axiom is unchanged.

For a positive-sign candidate, the search tries term limits
1, 2, 3, 4, 6, 8, 12, 16, 24, 32 and precisions 53, 80, 106 bits. It selects the
first supported prefix whose complete central interval excludes zero. Every
precision and truncation choice is stored in the payload and checked again.

The general semistable arithmetic engine proves every coefficient in the
prefix, including bad primes and repeated primes with small trace. The earlier
`prefixSupported` shortcut remains available for compatibility, but the batch
producer no longer requires it. See [ARITHMETIC_ENGINE.md](ARITHMETIC_ENGINE.md)
for the local-model, residue-field and Euler-factor proof chain.

The uniform theorem `certifySemistableCentralModel` connects these finite checks to
the actual modularity-dependent continuation, the proved actual global
coefficient bound and the central interval theorem. No per-curve mathematical
proof is handwritten. Every generated source contains an axiom guard admitting
only standard foundations and `ellipticModularity`.

## Outputs and cache

- `tests/VerifiedLcalcTests/Fixtures/Batch/`: complete generated Lean certificates.
- `output/batch/proposals.tsv`: untrusted producer proposals and skip reasons.
- `output/batch/report.json`: statuses after kernel replay, resource choices,
  source hashes and logs for rejections.
- `Regression/Generated.lean`: runtime keys for successfully checked results.
- `Assumptions/Generated.lean`: generated proof connecting every key to its
  checked analytic-order theorem.

The cache is installed only after that registry proof also builds. Failure
restores the previous registry sources. Existing unchanged certificate sources
are not rewritten; Lake reuses their compiled proofs and checks dependencies.
The generated registry and the legacy certificate are read only in the
explicit `lmfdb-check --conditional` mode. The default mode remains separate.

A completed batch can still exit 1: the final regression deliberately fails
when any of the 100 cases remains inconclusive. A kernel rejection is recorded
as a rejection, never as a zero result. A proposal alone is never counted as a
certified rank. Proof checking uses kernel `decide`, not `native_decide`.

## Current limits

The bad-prime sign hint is capped at primes 64 to avoid large exhaustive point
counts during candidate search. Input models outside the semistable criterion,
unseparated intervals, negative sign hints and resource
limits have distinct unresolved statuses. General good/bad local-model identification for semistable equations is now
proved; additive reduction still needs broader conductor/sign handling. Derivative certificates remain necessary for positive
ranks. This pipeline does not turn small numerical values into exact vanishing.

## First automated run

The first successful run kernel-checked 18 certificates in about 96 seconds
and installed their proved registry. The strict conditional regression reported
18 matches, 0 mismatches and 82 inconclusive cases, and exited 1. The remaining
statuses were 52 `no-supported-separated-prefix`, 26
`unsupported-semistable-model`, 2 negative/nonpositive sign hints and 2
bad-prime resource limits. There were no kernel-rejected proposals in that run.
These are conditional exact rank-zero results, not tolerance-based ranks.

The delivered runner is `CertifyBatchMain.lean`. A subsequent end-to-end run
through that Lean runner reused the compiled certificates, checked and installed
the registry, and reproduced 18 matches/82 inconclusive cases in about 46 seconds.

## Broader arithmetic engine

The current engine removes the former prefix restriction and certifies all
semistable positive-sign cases within the existing resource guards. The latest
complete run has 70 checked rank-zero certificates, 70 matches, 0 mismatches
and 30 inconclusive cases. It adds no arithmetic axiom. See
[ARITHMETIC_ENGINE.md](ARITHMETIC_ENGINE.md) for the proof and remaining scope.

### Additive arithmetic coverage

The additive extension now verifies local minimality and every coefficient prefix
for all 26 previously excluded additive fixture equations. The producer reports
`additive-conductor-sign-unproved` for these, identifying the remaining analytic
compatibility gap. It does not add their proposed conductors or signs to the
trusted assumptions, so the rank registry remains 70 checked conditional rank-zero
results and 30 inconclusive. Run `lake exe additive-witnesses --check` for the
separate 26/26 arithmetic replay; see [ADDITIVE_REDUCTION.md](ADDITIVE_REDUCTION.md).

## Initial 1,100-curve run

The expanded run has 397 checked conditional rank-zero certificates, zero
reference mismatches, and 703 inconclusive inputs. The current reasons are 532
additive conductor/sign obligations, 48 unresolved minimality criteria, 122
negative signs needing derivatives for exact rank, and one unseparated central
value. The former bad-prime resource guard is removed, using the proved fast
trace. Separate negative-sign certificates prove exact rank lower bounds for
those 122 curves, without treating a lower bound as an exact rank.

The installer composes a list of proof witnesses using `List.forall_mem_cons`.
It then proves the public membership soundness theorem from that list. This
avoids a large `rcases` proof. No extra axiom is introduced. If installation
fails, old sources are restored and their proof dependencies rebuilt as well.

`lake exe certify-batch --seal-cache` reuses an existing checked report after
validating every subject against the current fixture, rejecting duplicate
labels, and rechecking source hashes. It rebuilds the complete registry proof
dependency graph with Lake and runs the strict regression. It does not search
for new candidates or accept object-file presence as evidence. Use the full
batch command after source or fixture changes that invalidate the saved report.

## Tame additive run (2026-11-18)

The installed cache now contains **468** checked conditional exact rank-zero
certificates: 71 more than the initial expanded run. The strict regression
reports 468 matches, zero mismatches, and 632 inconclusive inputs, and returns 1
as required for incomplete coverage. There were no kernel-rejected proposals.
Remaining statuses are 444 wild-additive conductor/sign cases, 139 negative
signs needing derivatives for exact ranks, 48 unresolved minimality criteria,
and one unseparated central value. The full replay and registry installation
are recorded in `output/batch/report.json` and the group replay logs.

The single authorized modularity axiom now explicitly supplies standard tame
arithmetic compatibility under proved minimality and absence of additive
reduction at 2 and 3. Its content was strengthened; the arithmetic algorithms'
equality to mathematical formulas remains independently proved. See
[TAME_ARITHMETIC.md](TAME_ARITHMETIC.md) for the precise boundary.

The negative-sign generator now checks 139 separate conditional rank >= 1
certificates (17 more tame additive curves). Cached re-sealing of the 468-entry
exact-rank registry passed in 10.515 seconds and reproduced the same strict
coverage failure with zero mismatches.

## Wild additive follow-up (2026-11-18)

The installed cache now contains **822** conditional exact rank-zero
certificates, adding 354 wild-additive curves. Strict regression: 822 matches,
zero mismatches, 278 inconclusive inputs (229 need derivatives for exact rank,
48 need stronger minimality proofs, one central interval is unseparated).
The separate negative-sign replay checks 229 conditional rank >= 1 certificates,
adding 90 wild-additive curves. All 492 wild fixture equations have independent
kernel-checked Tate transcripts and mathematical conductor/sign formula
certificates; this does not assert minimality for the 48 unresolved models.

Full rank-zero replay now compiles nine conductor-range proof bundles while
preserving individual curve modules and theorem names. The first complete
822-entry bundled replay and installation took 453.021 seconds. Source-wrapper
hashes and full dependency rebuilds protect cache replay; bundle source digests
are recorded separately. See [WILD_ARITHMETIC.md](WILD_ARITHMETIC.md) for the
algorithm, proof/assumption boundary, sources, and rejection tests.
