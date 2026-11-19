# SQL conductor benchmark: In progress

Checked 1636 of 10000 curves in
217 of 1171 conductors.

- Conditional exact-rank certificates: 1543
- Inconclusive curves processed: 93
- Reference mismatches: 0
- Named concrete components audited: 14903
- Sum of recorded kernel build times: 29640.891 seconds
- Sum of candidate production times: 276.201 seconds
- Sum of warm validation times: 1239.218 seconds
- Sum of resume validation times: 72.628 seconds

Every analytic rank claim is conditional on `VerifiedLcalc.Assumptions.ellipticModularity`.
An inconclusive result is not an exact-rank certificate. Warm validation reuses
checked artifacts; it is not a fresh kernel replay. These stage sums describe
completed conductors and are not the full campaign wall time. `report.json`
records the current session wall time and per-conductor data.

Active/failure status: `[{"conductor": 594, "status": "failed", "error": "TimeoutExpired(['lake', 'build', 'VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N594Checked'], 3600)"}]`
