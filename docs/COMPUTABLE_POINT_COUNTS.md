# Computable cardinalities and point counts

Mathlib already represents an explicit finite/infinite classification by
`Fintype α ⊕' Infinite α`. A supplied finite branch contains an enumeration;
a supplied infinite branch contains a proof of infinitude. Matching on this
value and returning `Fintype.card α` or zero is computable and agrees with
`Nat.card α`. The tested example is in
[`tests/FinitePointCount.lean`](../tests/FinitePointCount.lean).

`fintypeOrInfinite α` constructs this classification noncomputably using
classical choice. Likewise, `[Finite α]` proves finiteness but does not supply
an executable enumeration. Neither gives an automatic algorithm for an
arbitrary type. `[Fintype α]` does supply the required data. Subtype enumeration
also needs a computable decision procedure for the defining predicate.

TauCeti's `WeierstrassCurve.pointCount` uses `Nat.card` and accepts arbitrary
fields. Retain that mathematical API. The proposed finite-field companion
[`WeierstrassCurve.pointCountFinite`](../VerifiedLcalc/UpstreamCandidates/TauCeti/PointCount.lean)
requires `[Fintype F] [DecidableEq F]`, explicitly decides the Weierstrass
equation, and uses `Fintype.card` of its solution subtype plus one. Its general
correctness theorem is `pointCountFinite_eq_pointCount`. This addition is local;
no upstream TauCeti source or public API has been changed.

The shared evaluator now supplies the certificate backend directly. The generic
`pointCountFinite` and `frobeniusTraceFinite` work over finite commutative rings;
their identification with TauCeti's mathematical count and trace requires a
field. The integer-input adapters `computePointCount` and
`computeFrobeniusTrace` specialize these algorithms to `ZMod p`. Prime-input
correctness is proved in `Correctness.lean`. Their shared cardinality and trace
bounds are also proved generically. The old integer-modulo enumerator and its
`Fin`/`ZMod` conversion have been removed. This consolidation makes no claim of
a measured performance improvement.

Both counts include singular affine solutions. Counting only Mathlib's
nonsingular point type would give the wrong answer at bad reduction primes.
Regression examples cover singular models in characteristics two and three,
a smooth model over `ZMod 5`, and the input adapters' boundary cases, using
`decide +kernel`. Positive composite moduli retain a finite-ring computation,
without a field interpretation. Modulus zero uses explicit sentinel outputs
(count one, trace zero); prime-input correctness never uses that branch.

The residue-field adapter `idealQuotientEquivZMod` is a separate issue. It
composes Mathlib's `Rat.ringOfIntegersEquiv`, `Ideal.quotientEquiv`,
`Ideal.quotEquivOfEq`, and `Int.quotientSpanNatEquivZMod`. The last definition
already supplies the substantive integer-quotient isomorphism. The adapter only
connects an ideal of `𝓞 ℚ` to the corresponding principal ideal of `ℤ`.


`Arithmetic.lean` now uses Mathlib's `b₂`, `b₄`, `b₆`, `b₈`, and `Δ`
directly, and reflects its decidable `Nat.Prime` predicate into a Boolean.
The duplicated invariant formulas and custom trial-primality implementation
have been removed.
