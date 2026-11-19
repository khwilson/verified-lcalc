# Additional 10,000 curves from the LMFDB SQL mirror

Downloaded by the user with `scripts/download_lmfdb_sql.py` on 2026-11-18,
using the documented read-only mirror, `devmirror.lmfdb.xyz:5432/lmfdb`.
The SQL transaction time is 2026-11-18T18:36:33.480944+00:00.

The snapshot contains 10,000 distinct labels across 1,171 conductors, from 285
through 1968. All 1,100 earlier fixture labels are excluded. Selection uses
conductor and label, with no rank filter. The last conductor contains 17 of
the 23 additional available curves; it is a partial boundary. Per-conductor
timings refer to this selected new subset, not all curves at each conductor.

`raw.json` preserves the SQL rows; `inputs.json` contains only labels,
conductors and exact integral Weierstrass coefficients. `references.json`
stores analytic ranks separately. No reference rank enters the Lean producer.
`provenance.json` records the exact query, exclusion list, boundary counts,
transaction time and SHA-256 hashes. The hashes are also in `data/SHA256SUMS`.

Attribution: The LMFDB Collaboration, https://www.lmfdb.org/citation .
Data license: CC-BY-SA, as documented at https://www.lmfdb.org/api/options .
Preserve this attribution and the captured provenance with redistributed data.

The reference comparison is independent of mathematical certification.
Actual elliptic analytic-rank certificates remain explicitly conditional on
the existing general-modularity assumption; their interval and arithmetic
components are proved without that assumption.
