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
[`WeierstrassCurve.pointCountFinite`](../VerifiedLcalc/EllipticCurve/FinitePointCount.lean)
requires `[Fintype F] [DecidableEq F]`, explicitly decides the Weierstrass
equation, and uses `Fintype.card` of its solution subtype plus one. Its general
correctness theorem is `pointCountFinite_eq_pointCount`. This addition is local;
no upstream TauCeti source or public API has been changed.

Both counts include singular affine solutions. Counting only Mathlib's
nonsingular point type would give the wrong answer at bad reduction primes.
The regression examples check singular models in characteristics two and three
and a smooth model over `ZMod 5`, using `decide +kernel`.

The existing specialized integer-modulo enumerator is now called
`VerifiedLcalc.EllipticCurve.computePointCount`. Its existing general bridge is
named `computePointCount_eq_pointCount`. It remains the certificate backend
pending a performance comparison and a migration of its affine-count bounds.
The executable TauCeti companion is an upstream candidate, not a claim that
these two computational implementations have already been consolidated.

The residue-field adapter `idealQuotientEquivZMod` is a separate issue. It
composes Mathlib's `Rat.ringOfIntegersEquiv`, `Ideal.quotientEquiv`,
`Ideal.quotEquivOfEq`, and `Int.quotientSpanNatEquivZMod`. The last definition
already supplies the substantive integer-quotient isomorphism. The adapter only
connects an ideal of `𝓞 ℚ` to the corresponding principal ideal of `ℤ`.


`Arithmetic.lean` now uses Mathlib's `b₂`, `b₄`, `b₆`, `b₈`, and `Δ`
directly, and reflects its decidable `Nat.Prime` predicate into a Boolean.
The duplicated invariant formulas and custom trial-primality implementation
have been removed.
