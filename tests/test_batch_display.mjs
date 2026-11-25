import assert from "node:assert/strict";
import {createHash} from "node:crypto";
import {readFileSync} from "node:fs";
import test from "node:test";
import {batchLabel, releaseTitle} from "../web/certificates/batch-display.mjs";

const inputs = readFileSync(new URL("../data/lmfdb/sql-10000/inputs.json", import.meta.url));
const hash = createHash("sha256").update(inputs).digest("hex");
const tag = "ec-certificates-123-1";
const leanVersion = "Lean (version 4.31.0, x86_64-unknown-linux-gnu, commit 0123456789ab, Release)";
const catalogue = {
  schema: 1,
  source_sha256: hash,
  selection: {offset: 0, count: 1000},
  lean_version: leanVersion,
  batch: {release_tag: tag},
};

test("derives display labels from the fields already in signed catalogs", () => {
  for (let index = 0; index < 10; index += 1) {
    const slice = {...catalogue, selection: {offset: index * 1000, count: 1000}};
    const expected = `lmfdb-2026-11-18-batch${String(index + 1).padStart(3, "0")}`;
    assert.equal(batchLabel(slice), expected);
    assert.equal(releaseTitle(slice, tag), `${expected} · ${leanVersion}`);
  }
});

test("keeps generic titles for other snapshots, incomplete slices and legacy metadata", () => {
  for (const other of [
    {...catalogue, source_sha256: "0".repeat(64)},
    {...catalogue, selection: {offset: 0, count: 999}},
    {...catalogue, selection: {offset: 1, count: 1000}},
    {...catalogue, selection: {offset: -1000, count: 1000}},
    {...catalogue, selection: {offset: 10000, count: 1000}},
    {...catalogue, selection: {offset: "0", count: 1000}},
    {batch: catalogue.batch},
  ]) {
    assert.equal(batchLabel(other), null);
    assert.equal(releaseTitle(other, tag), `Elliptic curve certificates ${tag}`);
  }
});
