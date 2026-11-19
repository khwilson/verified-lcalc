# LMFDB reference inputs

The original 100 cases remain in `../lmfdb-100.json`. The supplemental fixture
`../lmfdb-1000-additional.json` contains 1000 different labels. Both use the
analytic_rank field, never a substitution of Mordell-Weil rank.

On 2026-11-17 the LMFDB ec_curvedata API supplied the three stored JSON pages at
offsets 100, 200 and 300. Further requests returned a CAPTCHA, so those HTML
responses were discarded and API retrieval stopped.

The remaining source was obtained independently from John Cremona's public
`ecdata` repository, which supplies source data to LMFDB:
https://github.com/JohnCremona/ecdata

Pinned commit: 25cec5ecfec8b9f016eb1631ac633194c2bed39f

Source file: curvedata/curvedata.00000-09999. The first 1200 source lines are
retained verbatim in `raw/curvedata-first-1200.txt`. The upstream parser and
format documentation are retained alongside them. The relevant zero-based
columns in scripts/files.py are lmfdb_label=3, conductor=9, ainvs=10,
analytic_rank=30; rank=28 is a distinct field and is not imported.

The source data is distributed under the Artistic License 2.0, preserved in
`raw/ECDATA-LICENSE`. The retained `ecdata-files.py` is upstream provenance and
schema documentation, not executed by this project.

The Lean `import-lmfdb` executable selects the first 1000 source rows not already
in the baseline. It writes the supplemental JSON and Lean constants. Supplemental
cases retain source order; the combined list is serialized in label order to
allow a linear kernel check of uniqueness. Source equations, conductors and
analytic ranks match exactly in all 300 overlapping direct-API records.

Reproduce with `lake exe import-lmfdb`. Kernel-checked counts and uniqueness
are in VerifiedLcalc.LmfdbSupplementProofs. Reference ranks are regression data,
not analytic certificate evidence. The arithmetic backend receives CurveInput,
which does not contain the expected rank.

`../SHA256SUMS` records the snapshots and both fixture JSON files.

The complete upstream file (retained outside the repository during import) has
SHA256 `b42836e901ac75874d13207faef0bdc47a3799571937b1099df56c57897e8040`. All 1100 selected
fixture records, including the baseline rank-two and rank-three examples, agree
exactly with its corresponding source fields.
