// SHA-256 of data/lmfdb/sql-10000/inputs.json from the 2026-11-18 snapshot.
const snapshotSha256 = "71fbc342c387d48197e883729407aae9eabc31a80d6a3d34972fdbe338d2943e";

export function batchLabel(catalogue) {
  const {offset, count} = catalogue.selection ?? {};
  if (catalogue.source_sha256 !== snapshotSha256 || count !== 1000 ||
      !Number.isInteger(offset) || offset < 0 || offset >= 10000 || offset % 1000 !== 0) {
    return null;
  }
  return `lmfdb-2026-11-18-batch${String(offset / 1000 + 1).padStart(3, "0")}`;
}

export function releaseTitle(catalogue, tag) {
  const batch = batchLabel(catalogue);
  if (!batch) return `Elliptic curve certificates ${tag}`;
  return catalogue.lean_version ? `${batch} · ${catalogue.lean_version}` : batch;
}
