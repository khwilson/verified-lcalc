import { pathToFileURL } from "node:url";
import { setTimeout as sleep } from "node:timers/promises";

const delays = [0, 1000, 2000, 4000, 8000, 16000, 32000];

export async function waitForArtifact(name, id, listArtifacts, pause = sleep) {
  if (!name || !/^[1-9][0-9]*$/.test(id)) {
    throw new Error("Expected the artifact name and ID from the upload step.");
  }
  for (const delay of delays) {
    if (delay) await pause(delay);
    const matches = (await listArtifacts()).filter(artifact => artifact.name === name);
    if (matches.length === 0) continue;
    const [artifact] = matches;
    const actualId = String(artifact.database_id ?? artifact.databaseId);
    if (matches.length !== 1 || actualId !== id) {
      throw new Error(`Artifact service did not return the unique uploaded artifact ${name} (${id}).`);
    }
    return;
  }
  throw new Error(`Pages artifact ${name} (${id}) did not become visible to the artifact service.`);
}

export function artifactListRequest(token, resultsUrl) {
  const endpoint = new URL("/twirp/github.actions.results.api.v1.ArtifactService/ListArtifacts", resultsUrl);
  if (endpoint.protocol !== "https:") throw new Error("Expected an HTTPS artifact service URL.");
  // Match the workflow/job scope and unfiltered request from deploy-pages v4.0.5's
  // bundled @actions/artifact 2.1.3. The runtime token is available to JavaScript actions.
  const claims = JSON.parse(Buffer.from(token.split(".")[1], "base64url").toString("utf8"));
  const scope = claims.scp?.split(" ").find(value => value.startsWith("Actions.Results:"));
  const [, workflow_run_backend_id, workflow_job_run_backend_id, extra] = scope?.split(":") ?? [];
  if (!workflow_run_backend_id || !workflow_job_run_backend_id || extra !== undefined) {
    throw new Error("The runtime token has no artifact service scope.");
  }
  return async () => {
    const response = await fetch(endpoint, {
      method: "POST",
      headers: { authorization: `Bearer ${token}`, "content-type": "application/json" },
      body: JSON.stringify({ workflow_run_backend_id, workflow_job_run_backend_id }),
      redirect: "error",
      signal: AbortSignal.timeout(10000),
    });
    if (!response.ok) throw new Error(`Artifact service returned HTTP ${response.status}.`);
    return (await response.json()).artifacts ?? [];
  };
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const { ACTIONS_RUNTIME_TOKEN, ACTIONS_RESULTS_URL, PAGES_ARTIFACT, PAGES_ARTIFACT_ID } = process.env;
  try {
    const listArtifacts = artifactListRequest(ACTIONS_RUNTIME_TOKEN, ACTIONS_RESULTS_URL);
    await waitForArtifact(PAGES_ARTIFACT, PAGES_ARTIFACT_ID, listArtifacts);
    console.log(`Artifact service can see ${PAGES_ARTIFACT} (${PAGES_ARTIFACT_ID}).`);
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}
