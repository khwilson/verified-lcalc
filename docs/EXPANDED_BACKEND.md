# Expanded regression and remaining backend work

Workflow status (2026-11-19): legacy batch/derivative/conductor generators,
`lmfdb-check`, generated registries and bulk certificate directories described
below have been retired. Their command examples and cache counts are historical,
with implementation preserved in baseline commit `fcdc4f2`. The mathematical
proof engine remains; use [`certify_ec`](CERTIFY_EC.md) for current witness
verification and importable theorem generation.

The regression fixture now has 1100 inputs: the original 100 plus 1000 different
LMFDB-source curves. The added fixture has 765 analytic reference ranks zero and
235 analytic reference ranks one, with conductors 42 through 285. The baseline
still includes the analytic rank two and three examples. Reference ranks are
never passed to the arithmetic producer.

The data came from the pinned ecdata source used by LMFDB, after the direct API
returned a CAPTCHA following three successful pages. All 300 overlapping API
records match exactly. The Lean importer, retained source, license, commit pin,
field schema, and SHA256 manifest are documented in data/lmfdb/README.md.
The combined fixture is serialized in label order. A linear certificate checks
strict ordering of exact, padded integer label encodings. Distinct encodings
imply distinct labels; no collision assumption is used. Its counts and uniqueness
are kernel-checked in LmfdbSupplementProofs, outside the small runtime imports.

## Removed resource guard

The old p>64 guard is gone. BadPrimeCore evaluates the tangent quadratic in p
steps to distinguish a split node from a nonsplit node; a cusp has trace zero.
BadPrime proves equality to the actual singular-model Frobenius trace, in all
residue characteristics. FastSign proves equality of the resulting product to
the existing assumed semistable root-number formula. It adds no axiom and does
not change the modularity statement.

BadPrimeExamples kernel-checks trace 1 at 389 for 389.a1 and trace -1 at 5077 for
5077.a1. They no longer stop at an artificial bad-prime cap. A positive sign
with a central interval containing zero remains unresolved; a negative sign
requires derivative evidence before claiming exact rank one or higher.

The producer also tries 48 and 64 terms if the smaller central sums fail to
separate from zero. Every emitted payload remains checked by Lean.

## Broader minimality

InvariantMinimality adds the general sufficient criteria v_p(c4)<4 and
v_p(c6)<6, proved from integral changes of variables. They extend the earlier
v_p(Delta)<12 and 2-adic c4 criterion. Each executable criterion has a correctness
theorem. Failure is inconclusive, not a proof of nonminimality.

Run `lake exe additive-witnesses --expanded --check` for the separate arithmetic
replay on the larger fixture. This emits AdditiveExpandedExamples and its report
under output/additive-expanded. It does not turn unproved conductor/sign hints
into rank certificates. The baseline `--check` retains its original 26 subjects.

## Certificate replay

`lake exe certify-batch` now searches all 1100 inputs. It validates module names,
then replays at most eight proposed certificate modules in one Lake invocation.
A successful group checks every member. Failed groups fall back to individual
replay so rejection is attributed correctly. This amortizes Lake startup and
dependency discovery without accepting unverified cache entries. Source hashes
and the checked registry are preserved as before.

## Work that remains unproved

This extension does not fill every remaining analytic-rank proof obligation:

* Additive conductor exponents and local root numbers, especially at 2 and 3,
  still need their arithmetic theory and compatibility with the modular
  realization. Database values cannot prove these equalities. The currently
  implemented finite compatibility formulas are semistable; the modularity
  existence assumption itself is general.
* Minimal equations outside the sufficient criteria need a stronger minimality
  argument or a complete Tate/minimization algorithm.
* Negative-sign curves need a certified derivative evaluator and nonvanishing
  evidence for an exact rank-one result. The sign alone proves a central zero,
  not exact rank one.
* Higher exact ranks need exact lower-derivative vanishing arguments as well as
  a nonzero higher derivative. Finite numerical smallness remains the separately
  labeled numerical-rank policy, not an exact-vanishing proof.

General modularity for all elliptic curves over Q, including additive reduction,
is authorized (clarified 2026-11-18). The existing existence axiom already
quantifies over all nonsingular equations. Only the implemented finite
conductor/sign formulas are semistable specializations. Remaining general
conductor/root computations need arithmetic evidence, not further permission to
use general modularity. See GENERAL_MODULARITY.md.

## Negative-sign lower bounds

`lake exe negative-certificates --check` automatically generates and checks an
exact central-vanishing theorem and an analytic-rank lower bound for each of the
122 supported negative-sign inputs. These results use the existing semistable
sign formula and the proved functional equation. They read no reference rank
and add no axiom beyond the existing modularity assumption. In particular,
5077.a1 receives the true statement rank >= 1, not a claim of exact rank one.
The exact-rank regression continues to count these as inconclusive.

The generated source and source digest are cached, with a separate report in
output/negative-signs. The lower-bound certificates are deliberately not entered
into the exact-rank-zero registry.

The first 397-way registry assembly exceeded the old recursion limit. Every
individual certificate had checked successfully, but the cache installer refused
the failed aggregate proof and restored the previous sources. The aggregate now
sets explicit recursion and heartbeat limits. On a future failure, the installer
also rebuilds the restored registry so compiled artifacts match the restored
sources. This changes resource handling, not axioms or proof obligations.

The installed cache now has 397 conditional exact rank-zero results, with zero
reference mismatches and 703 inconclusive inputs. The separate 122 lower bounds
remain inconclusive for exact-rank regression. All 532 produced additive
arithmetic witnesses also pass Lean; the 48 unsupported models are retained
in the strict arithmetic report.

The final aggregate proof uses a compositional `List.forall_mem_cons` witness
list rather than a large case split; its first successful 397-entry build took
7.7 seconds. `certify-batch --seal-cache` validates cached labels and subjects
against the current fixture, checks source hashes, and rebuilds this proof and
its entire dependency graph. It reuses proofs without rerunning candidate
search or accepting bare object-file presence.

## Final checks

The full default build, all seven audits, fresh Cubic source replay, and all
four cached consumers passed. The consumers cover Cubic, additive arithmetic,
negative-sign lower bounds, and the combined rank-zero cache. All fixture and
checked-source digests match their manifests.

`tests/RegistryRollback.lean` deliberately binds the 11.a2 proof to the 5077.a1
subject. Lean rejects it; the installer restores both source files and rebuilds
their dependencies. A subsequent cached consumer confirms the original
397-entry checked registry. Rejected-binding diagnostics are retained separately
under output/tests/registry-rollback, without replacing the successful registry
log or changing its report.

The strict expanded rank regression returns 1, as required for 703 inconclusive
inputs. The expanded arithmetic replay likewise returns 1 for 48 unresolved
minimality criteria. These are coverage failures, not successful complete rank
computations or reference mismatches.

## Tame additive follow-up (2026-11-18)

The subsequent conductor/sign integration installs 468 exact conditional
rank-zero certificates, adding 71 tame additive curves. Regression: 468 matches,
zero mismatches, 632 inconclusive. Remaining statuses: 444 wild additive cases,
139 negative signs requiring derivatives for exact rank, 48 unresolved minimal
models and one unseparated value. The prior counts above describe the original
expanded run. See [TAME_ARITHMETIC.md](TAME_ARITHMETIC.md) for the executable
proofs and the explicitly strengthened general-modularity assumption.

Negative-sign replay additionally checks 139 conditional rank >= 1 certificates,
including 17 new tame additive cases. The 468-entry registry was re-sealed from
its checked cache in 10.515 seconds with the same regression results.

## Wild additive follow-up (2026-11-18)

The installed cache now contains **822** conditional exact rank-zero
certificates, adding 354 wild-additive curves. Strict regression: 822 matches,
zero mismatches, 278 inconclusive inputs (229 need derivatives for exact rank,
48 need stronger minimality proofs, one central interval is unseparated).
The separate negative-sign replay checks 229 conditional rank >= 1 certificates,
adding 90 wild-additive curves. All 492 wild fixture equations have independent
kernel-checked Tate transcripts and mathematical conductor/sign formula
certificates; this does not assert minimality for the 48 unresolved models.

Full rank-zero replay now compiles nine conductor-range proof bundles while
preserving individual curve modules and theorem names. The first complete
822-entry bundled replay and installation took 453.021 seconds. Source-wrapper
hashes and full dependency rebuilds protect cache replay; bundle source digests
are recorded separately. See [WILD_ARITHMETIC.md](WILD_ARITHMETIC.md) for the
algorithm, proof/assumption boundary, sources, and rejection tests.
