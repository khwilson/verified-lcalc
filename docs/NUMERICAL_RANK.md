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

`VerifiedLcalc/Certificates/NumericalQuartic.lean` saves a worked polynomial
example with an immutable 53-bit policy and four non-singleton derivative boxes.
It proves the numerical smallness statement and a separately named conditional
analytic lower bound. It also kernel-checks rejection of changed precision,
policy/precision disagreement, missing boxes and wide intervals. A mathematical
counterexample proves that a small nonzero constant passes the four-derivative
smallness condition while its actual analytic order is zero.

```
lake build
lake exe precision-policy
lake env lean VerifiedLcalc/Certificates/NumericalQuartic.lean
lake env lean certificates/NumericalQuartic.lean
lake env lean Audit.lean
```

Lake caches the proof module in the same way as the existing exact certificates.
The compiled consumer imports the saved theorems; the source replay checks them
afresh. No remote or content-addressed certificate store has been implemented.

The elliptic subject interpretation and actual central derivative evaluator
remain incomplete, so no elliptic numerical or exact rank has been fabricated.
The strict 100-curve LMFDB analytic-rank gate remains inconclusive and failing.
Future numerical comparisons must report their policy and use a separate result
category; they must not turn these observations into exact-rank successes.

Sources: [PARI implementation, lines 397–427](https://pari.math.u-bordeaux.fr/lcov-report/basemath/ellanal.c.gcov.html),
[LMFDB reliability notes](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q).
