import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

const repo = fileURLToPath(new URL("../", import.meta.url));

test("normal Pages assembly publishes the roadmap with its data and source revision", (t) => {
  const scratch = mkdtempSync(join(tmpdir(), "certificate-pages-"));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const bin = join(scratch, "bin");
  const site = join(scratch, "site");
  mkdirSync(bin);
  // The site command can assemble a companion without published batch releases.
  writeFileSync(join(bin, "gh"), "#!/bin/sh\ntest \"$1\" = api || exit 1\nprintf '[[]]\\n'\n", {
    mode: 0o700,
  });
  const revision = "a".repeat(40);
  const result = spawnSync("bash", ["scripts/publish_ec_catalog.sh", "site", "", site], {
    cwd: repo,
    env: {
      ...process.env,
      PATH: `${bin}:${process.env.PATH}`,
      GITHUB_REPOSITORY: "khwilson/verified-lcalc",
      GITHUB_SHA: revision,
    },
    encoding: "utf8",
  });
  assert.equal(result.status, 0, result.stderr);

  const read = (file) => readFileSync(join(site, file), "utf8");
  const roadmap = read("roadmap.html");
  assert.match(roadmap, /src="roadmap\.mjs"/);
  assert.match(roadmap, /href="roadmap\.css"/);
  for (const page of ["index.html", "fixtures.html"]) {
    assert.match(read(page), /href="roadmap\.html"/);
  }
  for (const asset of ["roadmap.mjs", "roadmap.css"]) {
    assert.equal(read(asset), readFileSync(join(repo, "web", "certificates", asset), "utf8"));
  }
  for (const data of ["fixture-field-coverage.json", "field-dependency-roadmap.json"]) {
    const committed = JSON.parse(readFileSync(join(repo, "web", "certificates", data), "utf8"));
    assert.deepEqual(JSON.parse(read(data)), { ...committed, git_revision: revision });
  }
  assert.deepEqual(JSON.parse(read("catalogs/index.json")), []);
});
