import assert from "node:assert/strict";
import test from "node:test";
import { artifactListRequest, waitForArtifact } from "../.github/actions/wait-for-pages-artifact/index.mjs";

const name = "github-pages-987-2";
const id = "1234";
const artifact = { name, database_id: id };
const noWait = async () => {};

test("waits for the exact new artifact through transient missing results", async () => {
  const unrelated = { name: "github-pages-987-1", database_id: "1233" };
  const lists = [[], [unrelated], [unrelated, artifact]];
  const delays = [];
  await waitForArtifact(name, id, async () => lists.shift(), async delay => delays.push(delay));
  assert.deepEqual(delays, [1000, 2000]);
  assert.equal(lists.length, 0);
});

test("rejects an unexpected ID and duplicate names immediately", async () => {
  const unexpected = { name, databaseId: "9999" };
  for (const list of [[unexpected], [artifact, unexpected]]) {
    const pause = async () => assert.fail("Unexpected retry after an identity mismatch");
    await assert.rejects(waitForArtifact(name, id, async () => list, pause), /unique uploaded/);
  }
});

test("bounds retries when the new artifact remains missing", async () => {
  let attempts = 0;
  await assert.rejects(waitForArtifact(name, id, async () => {
    attempts++;
    return [];
  }, noWait), /did not become visible/);
  assert.equal(attempts, 7);
});

test("uses the same unfiltered Twirp request as deploy-pages", async context => {
  const claims = Buffer.from(JSON.stringify({
    scp: "Other.Scope Actions.Results:workflow-backend:job-backend",
  })).toString("base64url");
  const token = `header.${claims}.signature`;
  const fetch = context.mock.method(globalThis, "fetch", async (endpoint, request) => {
    assert.equal(endpoint.href, "https://results.example/twirp/github.actions.results.api.v1.ArtifactService/ListArtifacts");
    assert.equal(request.method, "POST");
    assert.equal(request.headers.authorization, `Bearer ${token}`);
    assert.deepEqual(JSON.parse(request.body), {
      workflow_run_backend_id: "workflow-backend",
      workflow_job_run_backend_id: "job-backend",
    });
    return Response.json({ artifacts: [artifact] });
  });
  const listArtifacts = artifactListRequest(token, "https://results.example/path");
  assert.deepEqual(await listArtifacts(), [artifact]);
  assert.equal(fetch.mock.callCount(), 1);
});
