# Candidate proofs and dated verification registry

The registry is a uv-managed Python application over **PostgreSQL**. A FastAPI
HTTP API, a small browser dashboard, a CLI, and an MCP server share SQLModel tables
and the same application service. No Sage installation is required by the API.
Only the separate generation/checking worker needs the Lean project and its built
proof dependencies. All mathematical computation remains in Lean.

Candidate generation is separate from verification. Generating a curve's witness
and Lean script does not create a successful-check record and does not run
`decide +kernel`. Expensive checks happen only for an explicit campaign or a
scheduled selection. The existing modularity axiom remains explicit.

## Start a development instance

Prerequisites: uv, Python 3.11 or later, and a local PostgreSQL server. The supplied
Compose file provides a development database with persistent storage. Its default
password is for local development only; its port binds to localhost.

From `verified-lcalc/`:

```sh
uv sync --locked
docker compose up -d --wait postgres
cp .env.example .env
# Edit .env: replace the example API token with a long random secret.
export UV_ENV_FILE=.env
uv run lcalc-registry migrate
uv run lcalc-registry init-keys
uv run lcalc-registry serve
```

Open `http://127.0.0.1:8788/` for the dashboard or `/docs` for the HTTP schema and
interactive API. Read operations are public; operator writes require
`Authorization: Bearer $REGISTRY_API_TOKEN`. The dashboard keeps the token only
in its input field, not local storage. Expensive work runs in separate processes.
There is no default operator token. Run migrations explicitly, not on web startup.

`REGISTRY_DATABASE_URL` accepts `postgresql+psycopg://...` or `postgresql://...`.
`REGISTRY_DATA_DIR` holds the operator signing key and disposable checker work.
All source snapshots, witnesses, proof scripts, compiled artifacts, signed check
records, schedules and campaign reports are in PostgreSQL. Back up the database
and signing key together. Large artifacts currently use BYTEA; moving artifact
bytes to object storage can be added later without changing their content IDs.
The operator private key is never returned by HTTP or MCP.

For a published wheel, set `REGISTRY_CHECKER_ROOT` to the real verified-lcalc
checkout on checking hosts. The API itself can run without that checkout. The
wheel does not contain mathlib, compiled Lean dependencies, private keys or state.
The lockfile supports Linux and macOS. It includes exact dependency metadata
copied from cached official wheels to enable offline universal resolution in the
restricted development environment; the distribution hashes remain in `uv.lock`.

## Register the checker and import LMFDB data

Prepare the pinned Lean/mathlib dependencies using their caches, then compile the
small existing native worker if needed:

```sh
uv run lcalc-registry build-worker
uv run lcalc-registry register-environment
uv run lcalc-registry import data/lmfdb/sql-10000/inputs.json \
  --name lmfdb-sql-10000 \
  --provenance data/lmfdb/sql-10000/provenance.json \
  --references data/lmfdb/sql-10000/references.json
```

The commands print the environment and source IDs used below. `--references` is
optional; `data/lmfdb-100.json` already contains reference ranks in `cases`.
Reference labels must match the input labels exactly. Reference ranks are stored
as **external claims**, separately from the equation/conductor input. Generation
never reads them. A source-scoped campaign compares a rank only after its
mathematical proof was accepted, and reports mismatches separately. A successful
proof is not silently equated with a successful database-reference match.

A source ID commits to normalized inputs, labels, reference claims and provenance.
Changing an equation, a reference rank or the provenance creates a new snapshot.
A curve ID commits only to the exact Weierstrass coefficients and conductor; the
same curve can occur in multiple snapshots. A label is meaningful within its
source snapshot. Existing benchmark reports and the older volunteer SQLite demo
are retained separately; they have not been imported as verified registry events.

The environment ID commits to Lean version, mathlib/Tau Ceti pins when applicable,
checker Lean sources, the modularity statement and conservatively host platform.
There are also immutable checker-installation records for the compiler binary,
native worker and proof-template/binding implementation. Updating those tools
registers another installation without rewriting the old profile or check history.
Tasks and proof-source versions identify their assigned installation. Workers
claim only tasks for their exact registered environment and implementation.

## Generate now, check later

```sh
uv run lcalc-registry generate --source SOURCE_ID --environment ENVIRONMENT_ID \
  --limit 1000 --offset 0
uv run lcalc-registry worker
```

Generation tasks produce portable witnesses and versioned Lean proof scripts.
The dashboard and `/v1/proof-versions` show them as `candidate`. Unsupported
minimality/reduction or numerical separation remains `inconclusive`, with no
fabricated rank or theorem. The current evaluator searches exact ranks zero and
one and bounds its conductor and numerical parameters.

Clicking **Generate selected candidates** immediately opens **Your generation
queue**, showing submission activity followed by each selected curve's job status,
completion progress, errors, and source links. **View my queue** reopens it.
Closing the panel leaves the jobs running and the page polling. The panel tracks
this page's submitted jobs by their exact IDs, independently of later source or
environment filter changes. Reloading the page clears this session's panel;
the persistent generation-jobs table below still recovers database history.

The dashboard lists recent generation jobs and polls every two seconds while
they are pending/running, refreshing candidate results when job states change.
Errors and inconclusive outcomes appear in the job table. The worker terminal
prints readiness, assigned environment/installation, and each task start/outcome.
Persistent queued jobs require a running worker for their registered installation.

The selection limit is at most 1,000 per request. Use `--offset` to generate the
next page. Generation can be repeated: identical witnesses/source/installation
are deduplicated. The worker renders the exact witness into the installed Lean
proof template; independent Lean equalities bind every field to the submitted
data. Later kernel checking validates its mathematical constraints without
searching for a new witness. It still recomputes the finite proof checks.

Pick proof-version IDs from the API/dashboard, then either export them or request
a service-side check:

```sh
uv run lcalc-registry export PROOF_VERSION_ID [OTHER_VERSION_ID ...] \
  --output selected-candidates.zip
uv run lcalc-registry campaign PROOF_VERSION_ID [OTHER_VERSION_ID ...] \
  --name my-argument --source SOURCE_ID
uv run lcalc-registry status CAMPAIGN_ID
```

After **Request verification of selection**, candidate rows show **Queued for
verification**, then **Verification running**, and finally the checked, rejected,
or timed-out outcome. Candidate rows and campaign progress refresh automatically
while checks are active. Prior successful checks and their timestamps stay
visible when requesting another check. These live states also appear in the API
as `status` (`queued`/`running` while active), `verification_status`, and a
`verification_task` without worker lease credentials.

Omit `--source` for a campaign about mathematical claims alone. With it, the
selection must belong to that exact source snapshot, and accepted ranks are
compared with any recorded external claims. Missing references do not become
matches. Failed/inconclusive checks do not become reference agreements.

A bundle contains Lean sources, exact witnesses, source hashes, an environment
manifest, a generated `Selection.lean`, and an operator-signed candidate manifest.
It is explicitly marked **unchecked**, even if historical checks exist. The
signature authenticates who supplied the source; it does not certify its truth.
One bundle uses one exact environment and at most one source version per
candidate. Large selections should be split into bundles (30 MiB source limit).

## LMFDB button and submitted numerical witnesses

The API now serves an embeddable button for a known curve in a pinned snapshot.
Enable public generation requests on the API host, then keep the normal worker
running:

```sh
export REGISTRY_PUBLIC_PROOF_REQUESTS=1
export REGISTRY_PUBLIC_MAX_PENDING=64
export REGISTRY_PROOF_ORIGINS=https://www.lmfdb.org,https://lmfdb.org
uv run lcalc-registry serve
# Another terminal, with the same database/data/checker settings:
uv run lcalc-registry worker
```

First rebuild the native worker and run `register-environment` after updating this
code: the new renderer changes the installation hash. Existing frozen sources
and check history remain present. No database schema migration is needed for
this feature. An already running older worker cannot claim the new installation's
tasks.

For a local preview, visit:
`http://127.0.0.1:8788/static/proof-demo.html?source_id=SOURCE_ID&label=37.a1&environment_id=ENVIRONMENT_ID`.
Replace both IDs with registered values. The demo makes the same requests as the
embeddable button. It needs the public request switch enabled even on localhost.

The LMFDB template can include the following, substituting its curve label and
the operator's pinned snapshot/environment IDs. Template values must be emitted
with the web framework's JSON escaping (for example Jinja `tojson`), rather than
interpolating raw labels into JavaScript:

```html
<div id="lean-proof"></div>
<script type="module">
  import {mountProofButton} from 'https://PROOF_API_HOST/static/proof-button.mjs';
  mountProofButton(document.getElementById('lean-proof'), {
    api: 'https://PROOF_API_HOST',
    sourceId: 'SOURCE_ID',
    label: '37.a1',
    environmentId: 'ENVIRONMENT_ID',
  });
</script>
```

The visitor clicks, a task is queued, the button polls, and a download link appears
when the **unchecked** Lean source bundle is ready. By default the native server
searches for a witness. An optional async `getWitness()` callback on the button
supplies numerical JSON from browser computation or another program instead;
that path skips search. The callback must return a witness object. There is no
bundled browser numerical engine in this integration. Closing the page stops
polling; the queued server task continues. This is local integration scaffolding;
the production LMFDB site has not been changed.

Public HTTP operations:

- `POST /v1/proof-requests` with `source_id`, `label`, `environment_id` and optional
  `witness`: enqueue search or exact witness rendering; returns request ID/status.
- `GET /v1/proof-requests/{id}`: status, error, proof-version ID and download URL.
- `GET /v1/proof-requests/{id}/bundle`: download the signed unchecked ZIP, or 409
  until ready. Verify/check it using the local commands below.

Repeated requests for the same snapshot/label/environment/installation/witness
reuse their existing task, including after completion. Failed or inconclusive
requests are also stable; an operator may enqueue fresh search privately, and a
new installation produces new request IDs. An admission lock serializes public
requests across API processes, bounding pending/running tasks globally. A full
queue returns 429 with `Retry-After`. This is a queue bound, not a complete public
abuse prevention service; add deployment-level request limits as appropriate.
Unknown labels or subjects are rejected. Submitted witnesses are strictly shape
and size validated, bound to the snapshot equation/conductor, and stored as
immutable content-addressed artifacts before queueing. No submitted Lean source
is accepted. Neither public mode can queue an expensive kernel check, and neither
records a verified rank. A mathematically invalid, schema-valid witness may
produce an unchecked file that Lean subsequently rejects.

For authenticated submission from another application use `POST /v1/witnesses`
with the same fields and a required `witness`, plus the operator bearer token.
The token belongs on trusted hosts, never in an LMFDB page. The MCP tool
`submit_numerical_witness(source_id, label, environment_id, witness)` and CLI use
the same application service:

```sh
uv run lcalc-registry submit-witness witness.json \
  --source SOURCE_ID --label 37.a1 --environment ENVIRONMENT_ID
```

Only rank zero/one witnesses are supported by the present schema. Reference ranks
remain external claims; they do not enter witness search or rendering. Analytic
proofs retain the explicit `ellipticModularity` assumption. Every download remains
labelled unchecked even if a separate historical validation record exists.

## Import a generated theorem

The certificate is a Lean module, not a transcript of anonymous examples. New
sources use multiline formatting and export:

- `curve`: the explicit Weierstrass equation.
- `curve_analytic_rank`: the analytic rank of that curve.
- `analytic_rank`: the equivalent theorem stated using `result.equation`.
- `payload_correct`, `minimality_valid`, `local_data_valid`: named checked facts.
- `subject_eq`, `submitted_analytic_rank`, `coefficients_eq`, and other named
  equalities binding the proof to the exact submitted witness.

The dashboard's **Import theorem** expander shows the module import and theorem
name for each candidate. Merely generating the file does not check these claims.
After checking or fetching the matching compiled cache, importing that module
reuses its theorem without executing numerical search or `decide +kernel` again.

Every exported bundle also contains `Selection.lean` and `Usage.lean`. Local
`check-bundle` compiles the certificates and both consumer modules, then prints
`lean_path` in its report. With that path in `LEAN_PATH`, another file can write:

```lean
import Usage

#check ImportedCertificates.Curve1.equation
#check ImportedCertificates.Curve1.analytic_rank
```

`Usage.lean` lists each underlying content-addressed module and exports short
`ImportedCertificates.Curve1`, `Curve2`, etc. aliases in bundle order. Those names
are local to that selected bundle; the underlying module names are the permanent
identities. Its rank theorems are proved by applying the imported certificate's
`analytic_rank`, without numerical recomputation. The helper also works with
older stored sources that already exported `analytic_rank`.

Source versions are immutable: existing downloads are preserved. To generate the
new formatting and theorem names, stop the old worker, run `build-worker` and
`register-environment`, then restart the worker and API and generate again. The
mathematical environment ID is unchanged, but the generator installation and
source-version hashes change. Existing public request IDs remain associated with
their original installations.

## Check only the selected proofs locally

Obtain the operator's Ed25519 public key through a trusted channel and pin it.
The HTTP `/v1/public-key` endpoint exposes the public key but is not itself an
independent trust root.

```sh
uv run lcalc-registry check-bundle selected-candidates.zip \
  --public-key /trusted/registry-public.pem --output local-proofs
```

The command checks the signature, exact environment, paths and source hashes,
then runs Lean with `decide +kernel` and audits the resulting axioms. It writes
compiled modules, per-module logs and `local-check.json` only on full success.
The generator executable is not needed for this local check, but the matching
Lean toolchain and built mathematical dependencies are required. Only run sources
from a trusted producer: Lean compilation can execute metaprograms. Our producer
uses fixed templates populated by typed Lean values, not uploaded source.

Add `local-proofs` to `LEAN_PATH`, together with the installed verified-lcalc and
mathlib dependency paths. `Selection.lean` imports the generated theorem modules.
Their public `analytic_rank` theorems and `certifiedRank` values can be used in
another proof. A local check does not automatically claim the operator checked
anything and is not uploaded as an accepted event. Those events are created only
by the operator's checker.

## Campaigns, schedules and historical records

A campaign freezes the exact proof-version IDs and selection digest when queued.
Its worker tasks are separate from generation tasks. Each completed check adds a
new immutable record with time, outcome, exact source/environment/installation,
axiom audit, artifact digests and signed manifest. Failed checks are recorded too.
They never erase previous successful checks.

Once all campaign members finish, the worker publishes a signed report with
individual outcomes, accepted count, and source-reference comparisons/mismatches.
A finished campaign may contain failures; completion is not blanket acceptance.
The worker/scheduler can recover the commit-before-report crash window. Reports
are append-only. A date records an event; it does not expire a mathematical result.

```sh
uv run lcalc-registry schedule --name nightly-selection --source SOURCE_ID \
  --environment ENVIRONMENT_ID --every 86400 --limit 100
uv run lcalc-registry scheduler
```

Pause a schedule with `uv run lcalc-registry pause-schedule SCHEDULE_ID`; add
`--resume` to resume it. This affects future campaigns, not work already queued.
The dashboard and `PATCH /v1/schedules/ID` provide the same control.

Run the worker separately. Each tick freezes the first `limit` existing proof
versions for that source/environment in deterministic ID order; it does not claim
to check an entire larger dataset. The current schedule is a bounded repeated
selection, not a coverage sweep. Create explicit campaigns for other selections.
Missed intervals are coalesced, not replayed into an unbounded backlog. A source
with no candidates produces no campaign. Registered old installations must remain
available as workers to replay proof sources generated with them.

PostgreSQL uses `FOR UPDATE SKIP LOCKED` for task/schedule claims. Heartbeats renew
leases. An expired/superseded worker cannot publish. Immutable evidence tables
have database triggers rejecting UPDATE/DELETE; shared artifacts are content
addressed. Use a separate migration owner and runtime role in production; the
example grants are in `lcalc_registry/runtime-grants.sql`. The database owner can
change its own schema, so these controls do not replace trust in the operator.

## Reuse accepted compiled proofs

```sh
uv run lcalc-registry cache CERTIFICATE_ID --url https://YOUR-REGISTRY \
  --public-key /trusted/registry-public.pem --directory .lcalc-cache
```

This Python client verifies the signature and artifact hashes and prints the
module and `lean_path`. `--check Consumer.lean` checks a consumer with the fetched
cache added to its dependency path. It repeats neither candidate search nor the
expensive payload proofs. It requires the exact compatible installed proof
environment. Cache-only import trusts the signed operator provenance; ordinary
Lean imports do not independently recheck every cached declaration.

The compatibility endpoint `/v1/certificates/ID?environment=ENV` pins the first
accepted artifact set for that certificate/environment rather than silently
switching artifacts when another check runs. Dated verification events and
campaign reports preserve every later attempt. This does not make `.olean`
portable between arbitrary Lean/mathlib versions. Generate and check new proof
versions in each supported environment; no additional versions have been tested.

## HTTP and MCP

HTTP `/docs` describes the full API. Main operations:

| Operation | Endpoint |
| --- | --- |
| Import/list source snapshots | `POST/GET /v1/sources` |
| Find curve inputs and external references | `GET /v1/curves` |
| Enqueue generation | `POST /v1/generate` |
| Find candidates / retrieve source | `GET /v1/proof-versions`, `GET /v1/proof-versions/ID/source` |
| Export an unchecked bundle | `POST /v1/bundles` |
| Request and inspect a campaign | `POST/GET /v1/campaigns`, `GET /v1/campaigns/ID` |
| Read dated evidence | `GET /v1/verifications`, `GET /v1/campaigns/ID/report` |
| Create/list/pause schedules | `POST/GET /v1/schedules`, `PATCH /v1/schedules/ID` |
| Inspect work progress | `GET /v1/tasks/ID` |
| Retrieve accepted cache | `GET /v1/certificates/ID?environment=ENV`, `GET /v1/objects/SHA` |

There is deliberately no generic update/delete operation for evidence, no SQL
execution tool, and no public "mark verified" or proof-source-upload endpoint.
Only the installed trusted checker can record accepted checks.

For local stdio MCP, use the same environment variables and:

```json
{"mcpServers":{"lcalc-registry":{"command":"uv","args":["--directory","/absolute/path/verified-lcalc","run","lcalc-registry","mcp"],"env":{"UV_ENV_FILE":"/absolute/path/verified-lcalc/.env"}}}}
```

The HTTP server also mounts Streamable HTTP MCP at `/mcp/`. Configure the bearer
token in the MCP client. For a public host, set `REGISTRY_MCP_HOSTS` to the exact
Host header, such as `registry.example.org`, before starting. HTTP MCP is protected
by the same operator token even for reads; stdio trusts the local account that
started it. This is a local/operator-token setup, not an OAuth authorization server.

Tools include `list_sources`, `list_environments`, `find_curves`,
`find_proof_candidates`, `import_source_snapshot`, `generate_candidates`,
`request_verification`, `task_status`, `verification_status`,
`list_verification_records`, `set_schedule_enabled` and `export_proof_bundle`. The last returns a base64
ZIP for small selections; use HTTP/CLI for large bundles. Tool descriptions and
read/write annotations distinguish generation from expensive verification.

SQLModel supplies shared database/Pydantic models. FastAPI supplies HTTP and
OpenAPI; the pinned official MCP Python SDK's `FastMCP` supplies MCP. This is
separate from the standalone `fastmcp` project. Both interfaces call the same
Registry functions instead of exposing ORM mutations automatically. For general
applications, FastCRUD can generate REST CRUD operations and standalone FastMCP
or `fastapi-mcp` can expose selected REST operations as MCP tools. That automation
is useful for ordinary tables; evidence publication requires explicit semantics.

## Tests and current validation limits

```sh
uv run pytest
REGISTRY_LEAN_TESTS=1 uv run pytest registry-tests/test_lean.py
REGISTRY_TEST_DATABASE_URL=postgresql+psycopg://registry:registry@127.0.0.1:5432/lcalc_registry \
  uv run pytest registry-tests/test_postgres.py
uv build
```

The PostgreSQL tests create/drop a randomly named isolated schema in the supplied
**disposable** database. They exercise JSONB, immutability triggers, concurrent
SKIP LOCKED claims, duplicate generation, and campaign publication. They never
connect to or write to the read-only LMFDB mirror. Do not point them at production.

The fast suite uses an explicit SQLite test adapter; production configuration
rejects SQLite URLs. It tests registry invariants and the actual MCP protocol
through an ASGI transport. Fake numerical/checking backends in unit tests are
clearly marked; they are not evidence of mathematical correctness. The opt-in
Lean integration test uses the real native worker and kernel, checks a downloaded
bundle locally, separately checks it through the registry worker, signs/stores
artifacts and uses an accepted cached theorem in a new Lean proof.

This session has no usable local PostgreSQL daemon/Docker engine and no permitted
listening socket. The actual PostgreSQL tests and live-network/dashboard tests
have not run here. PostgreSQL DDL has been compiled and the API/MCP have been
exercised in-process. A real-browser test and PostgreSQL test run remain required
before deployment. The old browser contribution prototype is retained only under
`experiments/browser-worker/`; its immediate-verification API has been retired.
Its WASM bundle remains unbuilt and its old widget API is not served by the registry.

Before public deployment, use HTTPS, an isolated nonprivileged resource-limited
checker with immutable dependencies, proper secret management, ingress rate and
connection limits, and database backups. Signing attests an operator's check;
it is neither a ZK proof of execution nor a Palomar registration.

## Python quality and package layout

All supported Python code is in the single `lcalc_registry` package. There is no
second volunteer HTTP service. Shared proof-wire contracts, environment identity
and kernel validation live in `lcalc_registry/checker/`; the one FastAPI app lives
in `lcalc_registry/api.py`. The small Lean child build remains in `worker/lean`
so numerical execution does not import mathlib's proof infrastructure. Historical
ignored demo artifacts under `volunteer/` are not a supported package.

```sh
make format  # Ruff import/lint fixes and formatting
make check   # Ruff lint, formatting check, and ty (warnings fail)
make test
```

Equivalent commands are `uv run ruff check .`, `uv run ruff format --check .`,
and `uv run ty check --error-on-warning`. Ruff requires parameter/return
annotations, including on tests, and checks imports, common bugs and supported
Python syntax. ty checks the application, scripts and tests without a diagnostic
baseline or blanket suppression. JSON metadata is explicitly dynamic; exact
witnesses, compiled-cache manifests, model lookups and checker interfaces have
named types, generics and protocols. CI runs these checks and PostgreSQL tests
on Python 3.11 and 3.14; that workflow has not run from this local checkout.

After updating checker Python code or rebuilding the numerical worker, stop the
old processes, run `uv run lcalc-registry register-environment`, and start the
worker again. This registers the new installation fingerprint and preserves
old verification history. Old tasks remain assigned to their original installed
checker; generate fresh candidates for the new installation when needed.

Test the embeddable button's protocol and UI state transitions with:

```sh
node --test registry-tests/browser/proof-button.test.mjs
```

These are DOM/transport unit tests; production cross-origin hosting and browser
behavior still need deployment testing.


## LeanBridge reuse investigation (2026-11-19)

Recommendation: build a small on-demand certificate adapter that can cooperate
with LeanBridge's discovery tools. Do not add its whole root import to the
numerical worker. This is a source-level assessment, not a completed dependency
integration or a claim that all upstream modules were built/audited.

The [inspected lookup implementation](https://github.com/CBirkbeck/LeanBridge/blob/main/LeanBridge/Lookup/Lookup.lean)
exports `Lookup.sqlRequestBody` and `Lookup.runSql : String → MetaM Json`.
It posts SQL to `https://mcp.lmfdb.org/sql` using curl. Its query/report pipeline
translates goals and hypotheses, selects a counterexample, and leaves the goal
open. It warns when some comparisons cannot be translated. Numeric query output
is cast to text; our exact decimal-string witness format fits that convention.
The same module imports ProofWidgets for interactive reports.

Useful reuse candidates are the transport contract, editor reporting, and the
registered vocabulary/table machinery. The latter lives in `Lookup.Basic` and
`Lookup.Tables`; their complete contents could not be retrieved here, so the
specific elliptic-curve field mappings and their type compatibility are not yet
established. The [repository README](https://github.com/CBirkbeck/LeanBridge)
also advertises LMFDB query tactics, a search widget, and number-field/newform
certificates. Those are related integration points, not evidence of an existing
analytic-rank witness/cache API. The separate `LMFDB/Tactic` implementations were
not available for a complete source audit. Authorship of those modules by Bhavik
Mehta has not been established.

Dependency compatibility must be checked against a pinned checkout. The
[visible lakefile](https://github.com/CBirkbeck/LeanBridge/blob/main/lakefile.toml)
includes Tau Ceti, IdealArithmetic and documentation tooling, with mathlib pinned
to `dc4b8d60d5edb3c493c3662126b1b7ccae7d67cf`. Our installed mathlib is
`3440367ed1804626334f13a3a534a9cbb3385a59` under Lean 4.36.0-rc2. Web-indexed
upstream toolchain pages reflect different ages, so they do not establish current
HEAD compatibility. Direct GitHub CLI access failed locally; no complete pinned
checkout, upstream build or live LMFDB query was performed. These observations
must not be represented as a successful compatibility test.

The adapter should have three separate operations:

1. Resolve a label into a pinned source snapshot and explicit equation. Treat
   database ranks as external reference claims, never proof inputs. The theorem
   is about that explicit equation; the label-to-equation association remains
   snapshot provenance.
2. Fetch or generate a numerical witness and local source module. Reuse the
   current `Certificate` schema, installed Lean renderer, independent field
   bindings and content-addressed source versions. Network responses supply data,
   not proof constants or axioms. Preserve files for offline replay.
3. Either compile the source using the existing certification theorems and
   `decide +kernel`, or explicitly import an attested compatible compiled cache.
   The analytic result retains the authorized ellipticModularity assumption.

A future Lean command can wrap these operations, but no `lmfdb_curve` command
currently exists in this project. The numerical worker must keep its small core
imports; networking and ProofWidgets belong in the elaboration/editor adapter.
The existing `curve_analytic_rank` theorem and bundle `Usage` module are the
consumer interface already available today.

Before implementation, obtain one pinned LeanBridge revision; inspect its
`Lookup.Basic`, `Lookup.Tables`, and `LMFDB/Tactic` modules; align dependency
versions using caches; and demonstrate one exact model (37.a1) through discovery,
local witness checking and a separate importing proof. Check altered witnesses
and label/subject mismatches are rejected. Only then decide whether to import a
small existing module or extract a shared configurable transport upstream.
