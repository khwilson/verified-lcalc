# Registry validation — 2026-11-19

- `uv sync --locked --offline` succeeded using the existing cache.
- `uv build --offline` built the source distribution and wheel. Package inspection
  found no private signing keys, databases, checker build output or state files.
- Fast suite: **15 passed**. The real-kernel test is opt-in; the two actual
  PostgreSQL tests require an explicitly supplied disposable database.
- The MCP test used the real MCP client/server protocol over an in-process ASGI
  transport, including initialization, tool discovery, curve queries and task
  creation. It did not use a mocked MCP protocol.
- The opt-in real Lean test passed. It generated a 37.a1 candidate without a check
  record, exported and locally checked its signed source bundle, separately
  checked it through the registry worker, stored signed artifacts, downloaded
  them through the API, and used the cached analytic-rank theorem in another
  Lean proof, evaluating its proof-carrying rank to `1`.
- The older volunteer unit suite still passed: 12 passed, one kernel test skipped.
- PostgreSQL DDL compiled for all tables. **PostgreSQL execution was not tested**:
  no usable local PostgreSQL daemon or Docker engine was available. The optional
  integration tests cover JSONB, database immutability, concurrent SKIP LOCKED
  claims, duplicate generation and campaign publication when run on PostgreSQL.
- HTTP/dashboard endpoints were tested in-process; no listening HTTP socket or
  real-browser UI test ran here. Public deployment has not been performed.

The fast suite's checking backend is explicitly fake and publishes only test
artifacts under disposable test keys. Its passing is not mathematical evidence.
The separate Lean integration test used the real native worker and kernel.

Finite proof checks use standard axioms; analytic-rank claims retain the
previously authorized `VerifiedLcalc.Assumptions.ellipticModularity` assumption.
No mathematical Lean source, axiom statement or benchmark engine was changed.
The shared Python validator was refactored to expose its existing kernel-checking
stage without writing to the older SQLite demonstration database.

See [REGISTRY.md](REGISTRY.md) for the setup and test commands and the remaining
PostgreSQL/live-network checks required before deployment.

## Consolidation and type-checking follow-up

The duplicate volunteer Python service has now been removed. Its reusable wire
contracts, environment code and kernel stage are in `lcalc_registry/checker`;
its numerical build is in `worker/`. The historical measurements above describe
the pre-consolidation layout.

Current checks:

- `make check`: Ruff lint, formatting and ty all pass, with ty warnings failing.
- `make test`: 28 passed; the opt-in kernel test and two PostgreSQL tests are
  skipped in the fast run.
- The opt-in real Lean bundle/campaign/cache integration passed separately after
  consolidation. The relocated numerical worker rebuilt successfully.
- The package wheel contains only `lcalc_registry` Python code, frontend assets
  and metadata; no old volunteer service, signing keys or database state.
- PostgreSQL execution and the new GitHub Actions workflow still require their
  respective external runners. They have not been run in this local environment.

Ruff enforces function annotations throughout application code, scripts and tests.
Exact witness and cache contracts use named TypedDicts, model lookups preserve
model types through a type variable, and workers use a checking-backend protocol.
Arbitrary JSON metadata remains explicitly dynamic. There are no type-ignore
baselines or blanket type-checker suppressions.

## Witness submission and LMFDB proof button

The same application now accepts source-scoped numerical witness submissions
through REST, CLI and MCP. Submitted JSON is frozen as a content-addressed
artifact. Generation renders that exact witness; it does not search again or
create a successful-check event. Public requests are explicitly enabled, bounded,
idempotent and limited to curves in registered snapshots. The schema is unchanged.

Validation for this addition:

- Python fast suite: **31 passed**; three native/Lean tests and three PostgreSQL
  tests are opt-in and skipped in the fast run.
- Two real Lean integration tests passed in **28.92 seconds** together: the
  source-bundle/campaign/cache consumer route, and supplied-witness generation
  with search disabled, equivalent unreduced rationals accepted by the kernel,
  and a deliberately incorrect coefficient rejected during kernel verification.
- An additional native renderer test passed for wild additive curve 112.a2:
  decoding its supplied Tate transcript produced exactly the source emitted by
  the prior fixed-witness reconstruction/template route.
- Six Node widget tests pass: explicit click, server search, supplied witness,
  unchecked download link, queue errors, cleanup, HTTPS, and rejection of an
  invalid witness callback. These use a fake DOM/transport; no real browser ran.
- The real MCP protocol test also submitted a numerical witness through the new
  tool and confirmed no verification record was created.
- Ruff and ty pass without new suppressions. The native Lean renderer rebuilt.
- PostgreSQL execution is still unavailable locally. A new opt-in PostgreSQL
  test covers concurrent request deduplication and the admission lock. No
  production LMFDB page or public deployment has been changed.

The new Lean transport decoder is deliberately untrusted data plumbing. Every
submitted field is independently bound by Lean equalities in the generated proof;
the mathematical constraints and authorized axiom audit remain kernel checked.
No mathematical arithmetic engine or axiom statement changed.


## Generation progress follow-up

Fixed the dashboard's missing generation-task polling. It now recovers recent
jobs on page load, displays pending/running/completed/failed/inconclusive states
and errors, and refreshes candidates as jobs change. Worker CLI output now
includes readiness and task starts/outcomes. No rebuild or re-registration of the
numerical worker is required for this UI/logging change.

Ruff, formatting and ty pass. The fast Python suite passes 32 tests (six opt-in
tests skipped), including job listing, error visibility and lease-token exclusion.
Nine Node tests pass, including queue-state summaries. The dashboard module also
passes Node syntax checking. PostgreSQL and real-browser execution remain untested
locally. No mathematical code or proof implementation changed.

## Readable certificates and imported theorem interfaces

Generated sources now retain Lean's multiline pretty representation, name all
submitted-witness equalities, and export an explicit `curve` and
`curve_analytic_rank` alongside the existing `analytic_rank`. The binding theorem
`submitted_analytic_rank` still checks the precise rank claimed in the JSON.
Bundles include a public `Selection` module and a `Usage` module with named
`ImportedCertificates.Curve1.analytic_rank`, etc. consumer theorems. Local bundle
checking compiles both import modules after the individual certificates.

Ruff/format/ty pass. The fast suite passes 34 tests (six opt-in tests skipped).
All three native/Lean tests passed with the new template, including central,
derivative, wild Tate serialization and deliberate bad-witness rejection. The
strengthened real integration test passed separately: a further file imported
`Usage` and proved a rank theorem, and an independent compiled-cache consumer
used `curve_analytic_rank` plus the named witness equalities. No numerical search
or proof replay was added to those consumers. Browser JavaScript syntax checks
pass; PostgreSQL and real-browser checks remain external requirements.

The core mathematical engine and modularity axiom statement are unchanged. The
source template/binding implementation and worker binary changed, so operators
must register the rebuilt installation and restart workers before regenerating.
Previously stored source artifacts remain immutable.

## Immediate generation queue panel

Generate now opens an accessible native dialog before waiting for the API,
disables duplicate submission while that request is pending, and displays the
exact returned jobs with curve labels, live counts/progress, errors and source
links. The panel follows this page's submitted IDs independently of filters;
closing it leaves polling and queued work active. View my queue reopens it.
Reloaded history remains in the existing generation-jobs table.

All 17 Node UI/protocol tests pass, including immediate submission feedback,
duplicate-click prevention, exact-ID polling, completion after closing, multiple
batches, errors, retry, and distinguishing accepted jobs from a failed page
refresh. JavaScript syntax checks and make check (Ruff/format/ty) pass. These
are DOM/transport tests; no live-browser visual inspection was performed. No
backend, mathematical engine, or registered checker implementation changed.


## Live verification status

Candidate listings now derive queued/running verification states from actual
verification tasks; active running work takes priority over another queued check.
Historical acceptance records are retained throughout rechecking. The dashboard
refreshes candidate status immediately after campaign creation and polls active
checks/campaigns, retaining row selections across refreshes. Rejection and timeout
are visible outcomes rather than reverting silently to unchecked.

Ruff/format/ty and JavaScript syntax checks pass. The Python fast suite passes
36 tests (six opt-in checks skipped); all 20 Node tests pass. New tests exercise
HTTP queue/claim/reject/accept/requeue transitions, lease-token exclusion, multiple
active campaigns and display of prior acceptance. No mathematical or registered
checker implementation changed; only the API needs restarting and the browser
needs a hard refresh. PostgreSQL/live-browser tests were not run locally.
