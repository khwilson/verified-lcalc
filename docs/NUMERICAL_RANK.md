# Precision policy and numerical rank observations

The global default is defined once in `VerifiedLcalc/Precision.lean`:

```
precisionBits = 53
cutoff rule = pari-half-bits-v1
cutoff = 2 / 2^(precisionBits / 2) = 1/33554432
```

Here `/ 2` in the exponent is natural-number division. The rule follows the
inspected PARI `ellanalyticrank` implementation, not its slightly different
documentation formula. The cutoff is approximately 2.98e-8. It classifies
numerical observations; it is not the evaluator's rounding or truncation error.
Higher working precision gives a smaller cutoff. Changing the global policy is
a source change, and explicit per-request overrides are also possible.

`Artifacts.Settings.precisionBits` defaults to the global policy. Existing
explicit settings, including the exact polynomial demo's precision 0, retain
their original meaning. A numerical observation must have at least two bits
and its requested working precision must match its stored policy.

Run `lake exe precision-policy` to inspect the current default.

## Certificate meaning

`NumericalRanks.Artifact` is a separate certificate type from the exact-rank
`Artifacts.Artifact`. Its field `numericalLowerBound = 4` means that raw
derivatives of orders 0, 1, 2 and 3 all pass the cutoff test. It makes no claim
about the fourth derivative. This is labelled **numerical rank >= 4**, not
unconditional analytic rank >= 4.

The payload stores the complete exact subject, arithmetic/unitary normalization,
working precision, term budget, derivative budget, source/build identities,
format version, policy and rational derivative rectangles. The policy is a
snapshot in each request: changing the global default does not reinterpret a
saved artifact. Different policies, settings, subjects or build identities
cannot reuse a certificate under a new expected request.

The check requires the entire real and imaginary coordinate intervals of every
earlier derivative to lie in `[-cutoff, cutoff]`. It rejects inverted bounds,
insufficient derivative coverage and intervals wider than the cutoff. This is
a coordinatewise test, not a complex absolute-value test, and there is no
normalization by derivative factorials or by a BSD-predicted leading term.

The finite data checker cannot establish that the boxes describe an L-function.
`NumericalRanks.Evidence` requires the subject interpretation, analyticity, and
proofs that the boxes enclose the actual iterated derivatives. Given those
proofs, `check_sound` establishes the unconditional statement `SmallDerivatives`:
each earlier derivative's real and imaginary parts has absolute value at most
the stored cutoff. Enclosures must include all rounding and analytic tail errors;
those errors cannot be silently replaced by the classification cutoff.

The certificate may additionally contain `check_conditional_lowerBound`. Its
type explicitly takes an `ExactVanishingHypothesis`: for this function and
these derivative orders, cutoff-small derivatives are exactly zero. Only with
that additional hypothesis does it prove a genuine analytic-rank lower bound.
This hypothesis is not known in general and is not registered as a Lean axiom.
A future arithmetic vanishing theorem can discharge it; numerical precision
alone cannot. The stored precision does not itself imply the hypothesis.

## Replay and regression

`tests/VerifiedLcalcTests/Fixtures/NumericalQuartic.lean` saves a worked polynomial
example with an immutable 53-bit policy and four non-singleton derivative boxes.
It proves the numerical smallness statement and a separately named conditional
analytic lower bound. It also kernel-checks rejection of changed precision,
policy/precision disagreement, missing boxes and wide intervals. A mathematical
counterexample proves that a small nonzero constant passes the four-derivative
smallness condition while its actual analytic order is zero.

```
lake build
lake exe precision-policy
lake env lean tests/VerifiedLcalcTests/Fixtures/NumericalQuartic.lean
lake env lean tests/consumers/NumericalQuartic.lean
lake env lean Audit.lean
```

Lake caches the proof module in the same way as the existing exact certificates.
The compiled consumer imports the saved theorems; the source replay checks them
afresh. No remote or content-addressed certificate store has been implemented.

Exact rank-zero and rank-one elliptic certificates are now supported by the
separate central/first-derivative backend and `certify_ec`. They prove exact
nonvanishing and are not tolerance-only rank observations. Higher derivatives
needed for a real numerical rank-four observation are still missing; no such
elliptic certificate is claimed by the numerical quartic example.

## Explicit per-curve separation hypotheses

`NumericalRanks.NonzeroDerivativeGap f center n gap` says that each nonzero raw
derivative of order less than `n` has a real or imaginary coordinate of magnitude
at least `gap`. With checked coordinatewise bounds at most `eps` and the strict
margin `eps < gap`, `exactVanishing_of_gap` proves the earlier derivatives vanish.
This supplies the existing `ExactVanishingHypothesis` interface. The strict
margin avoids falsely treating the cutoff endpoints as zero.

`lowerBound_of_small_gap` proves analytic order at least `n` under analyticity.
`rank_eq_of_small_gap` additionally requires nonvanishing of derivative `n` to
conclude exact rank. A central-value assumption alone does not imply rank four:
orders zero through three must all be addressed.

For elliptic curves, `Assumptions.CurvePrecisionClaim` stores the exact equation,
precision policy, derivative count and rational nonzero gap. Its indexed
`Hypotheses` proposition records the missing separation assumption and strict
margin for that specific curve's arithmetic L-function at 1. The conditional
lower-bound/exact-rank theorems keep this hypothesis explicit. An adapter derives
the claim identity from checked numerical evidence, retaining actual enclosure
proof obligations. It cannot replace those proofs with metadata or reference
ranks.

Use `VerifiedLcalc/Assumptions/Curves/` for explicitly opted-in per-curve
assumption declarations. No blanket gap axiom or rank-four curve axiom has been
added. Projects can carry a hypothesis parameter, prove an instance later, or
postulate a separately named instance in their own opt-in module and accept that
additional axiom dependency. Current exact `certify_ec` deliberately rejects
such extra axioms; a future conditional higher-rank interface must display its
assumptions separately.

The generic gap-to-order theorems use only standard foundations. The elliptic
wrappers also depend on the existing modularity package. Tests show that a small
nonzero constant fails the proposed gap hypothesis; smallness alone still cannot
establish rank four.

Sources: [PARI implementation, lines 397–427](https://pari.math.u-bordeaux.fr/lcov-report/basemath/ellanal.c.gcov.html),
[LMFDB reliability notes](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q).
