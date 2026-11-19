# Wild additive reduction at 2 and 3

The backend has three separate parts:

* `WildTateCore.lean` constructs and checks Tate reduction transcripts for
  integral equations with additive reduction at 2 or 3.
* `WildRootCore.lean` evaluates the Halberstadt local-sign tables on the actual
  c4, c6 and discriminant invariants and the transcript's Kodaira code.
* `WildArithmetic.lean` proves agreement with mathlib variable changes,
  finite-field polynomial tests, factorization valuations, primitive quadratic
  characters on ZMod 4/8, and the Legendre symbol at 3.

## What a transcript checks

The initial integral translation moves the singular point and tangent into
Tate's normal form. Exact coefficient and b-invariant divisibility distinguishes
II, III and IV. Later stages check the normalized cubic and its repeated root,
then distinguish I0*, the alternating quadratic chain for I_n*, IV*, III* and
II*. Each repeated root and translation is retained and checked. Exact
integrality conditions precede the divisions. The terminal component count
provides the offset in Ogg's formula f = v_p(discriminant) - offset.

The I_n* search has an explicit fuel bound derived from the discriminant
valuation. Exhaustion returns no result. The validator checks the full
transcript independently; success never assumes that a resource bound proves
termination or completeness. In particular, changing a proposed Kodaira code or
shortening a chain cannot bypass the path conditions.

The executable search is candidate production, outside the mathematical trust
boundary. `tateWitness?_sound` and `wildData?_sound` prove that every accepted
output satisfies its declarative transcript/character conditions. Generated
certificates check these conditions again using `decide +kernel`. The predicate
is not a comparison with the search algorithm's own output or an expected
conductor. Search completeness is not claimed for all elliptic curves.

Global products are over all mathematical discriminant prime factors. Candidate
prime lists can use the input conductor as a bound, but kernel-checked equality
to those full products is mandatory before rank certification. Expected
analytic ranks never participate in witness or certificate production.

## Proved formulas versus geometric compatibility

The finite arithmetic and executable-to-formula equalities have no custom
axioms. Minimality and actual curve Euler coefficients use the previous
independent minimal-model proofs. A Tate classification transcript by itself
is **not** claimed to prove geometric conductor theory or epsilon-factor
theory in Lean.

The existing authorized `ellipticModularity` assumption is explicitly extended
with `ArithmeticModularRealization.wildLevel_eq` and `wildSign_eq`. They identify
these mathematical Tate/Ogg/Halberstadt formulas with the modular level and
Fricke sign, conditional on proved global minimality and valid transcripts.
These are standard arithmetic compatibility facts included in the authorized
package. This is a change to the axiom's content, even though its name is the
same. They do not accept arbitrary supplied conductor, sign, rank, numerical
enclosure, or vanishing claims.

`Assumptions/WildCertification.lean` uses those fields to supply conductor/sign
evidence to the existing proved central evaluator and to prove exact central
vanishing/rank >= 1 when the checked sign is negative. Negative signs do not
establish exact rank one.

## Sources and licensing

The mathematical algorithms are Tate's algorithm and Ogg's conductor formula,
and Emmanuel Halberstadt, *Signes locaux des courbes elliptiques en 2 et 3*,
C. R. Acad. Sci. Paris I 326 (1998), 1047–1052,
[DOI](https://doi.org/10.1016/S0764-4442(98)80060-8).

The case organization was checked against the official PARI/GP implementation,
[`elliptic.c`, localred_23, neron_2/3 and ellrootno_2/3](https://pari.math.u-bordeaux.fr/lcov-report/basemath/elliptic.c.gcov.html),
retrieved 2026-11-18. The relevant reference excerpt is stored as
`data/upstream/pari-elliptic-wild.c`, SHA-256
`26f97afc9955b695fa50cbe9ff71ce0304fec2ad4f88301c1417138ace98fb60`.
It is reference material only; no PARI/C code executes in the Lean backend.
`WildRootCore.lean` preserves the PARI attribution and GPL-2.0-or-later notice;
the complete GPLv2 text is in `LICENSES/PARI-GPL-2.0-or-later.txt`.

The zero c4/c6 valuation sentinel 12 is the finite table encoding used by the
reference implementation; zero unit parts remain zero. It is not a claim that
v_p(0)=12. `wildValuationSpec` makes this distinction explicit.

## Replay

`lake exe wild-witnesses --check` emits and kernel-checks arithmetic-only
transcript and conductor/sign formula certificates for wild fixture equations.
It does not assert minimality or analytic ranks for unresolved minimal models.
`lake exe certify-batch` separately checks numerical certificates and installs
the sound exact-rank registry. `lake exe negative-certificates --check` handles
negative-sign lower bounds separately. `--seal-cache` revalidates certificate
subjects and source hashes and rebuilds the full theorem dependency graph.

`WildExamples.lean` includes residue characteristics 2, 3 and both together,
and checks rejection of a wrong Kodaira code, a shortened I_n* chain,
unsupported primes, and singular equations. `AuditWild.lean` guards the
arithmetic-versus-conditional theorem dependency boundary.

## TauCeti check

No Tate algorithm was found in our pinned TauCeti snapshot. The upstream
elliptic-curve directory lists integral/minimal-model infrastructure and a node
polynomial, but no dedicated Tate/Kodaira module was visible in the accessible
listing. Live source and PR fetches failed during this check, so this is not a
claim that no newer unmerged implementation exists. Existing TauCeti local-model
and minimality results remain in use through the prior integration.

## Shared proof storage

Rank-zero certificates retain their individual public modules and namespaces.
Their full proof text is compiled in `Certificates/Batch/Bundles/Nk.lean`,
where k = floor(conductor/32). Individual modules re-export their bundle.
The installer deduplicates these build targets and imports the checked bundles
directly, avoiding hundreds of repeated library imports. It still checks every
individual theorem and the complete registry membership proof. A failed bundle
is not treated as partially verified.

Saved report source hashes bind the public wrapper files. Cache re-sealing
rebuilds the *entire* proof dependency graph, including their bundle sources;
wrapper hashes alone do not authorize acceptance. `tests/BundleDependency.lean`
injects a false claim into a bundle while leaving its wrapper unchanged and
checks that the kernel rejects it, then restores the checked source/artifacts.
`tests/RegistryRollback.lean` separately checks rejection of a theorem bound to
the wrong curve. Bundle source digests are recorded alongside the checked run.

`output/wild/reference-check.json` is a separate external-data test: computed
global signs agree with reference analytic-rank parity on all 492 wild curves.
Expected ranks are read only by this comparison, never by witness production or
formal rank certification. This comparison is not a proof of local root-number
theory or an exact rank computation.

## Checked coverage (2026-11-18)

* 492/492 wild fixture equations: checked Tate transcripts and mathematical
  conductor/sign formula certificates, with no conductor-reference mismatch.
* 822/1100 installed conditional exact rank-zero certificates, including 354
  new wild-additive curves. Regression: zero mismatches, 278 inconclusive.
* 229 separate checked conditional rank >= 1 certificates, including 90 new
  wild-additive curves. These are not exact rank-one claims.
* Remaining exact-rank gaps: 229 derivative computations, 48 unresolved
  minimality criteria, one unseparated central value (389.a1).

The first full bundled replay and registry installation took 453.021 seconds.
All mathematical claims continue to have the proof/assumption boundary stated
above. The strict regression returns 1 while coverage is incomplete.

Cache re-sealing after the bundled run took 19.868 seconds and reproduced 822
matches, zero mismatches and the intentional coverage failure for 278 inputs.
The checked wrapper hashes are in `output/batch/report.json`; the nine bundle
source digests are in `output/batch/proof-bundles.sha256`.

Run `lake env lean certificates/Wild.lean` to execute saved proof-carrying
values: exact rank 0 for 27.a1, 32.a4 and 36.a1, followed by the proved lower
bound 1 for 112.a1. The final value does not claim exact rank one.

## Final validation

The full default build, explicit saved-consumer dependency builds, and all ten
axiom audits passed (`Audit`, `AuditArithmetic`, `AuditAdditive`,
`AuditExpandedAdditive`, `AuditExtended`, `AuditIntegration`, `AuditAssumptions`,
`AuditGeneralModularity`, `AuditTame`, `AuditWild`). Fresh Cubic replay and the
saved Cubic, additive, general-modularity, tame, wild, negative-sign and exact-rank
cache consumers passed. The wild consumer executes 0, 0, 0 and lower bound 1.

Both rejection tests passed: wrong-curve binding was rejected and the 822-entry
registry restored; a false claim inside a bundle was rejected despite an
unchanged wrapper, then the original source and checked dependency artifacts
were restored. Main success logs and report were preserved; deliberate failure
diagnostics are under `output/tests/registry-rollback` and
`output/tests/bundle-dependency`.

The baseline additive replay remains 26/26 and expanded additive minimality
replay 532/580. The latter intentionally returns 1 for its 48 unresolved models.
All 822 wrapper hashes, nine bundle source digests, and all four checked
arithmetic/lower-bound source manifests match. The pinned mathlib checkout is
unchanged.
