# Tame additive conductor and root numbers

`EllipticCurve/TameCore.lean` implements finite conductor/sign computation for
minimal integral models that have no additive reduction at 2 or 3. Good and
multiplicative reduction at 2 and 3 are supported. The executable imports only
core arithmetic modules; mathlib specifications and proofs live in
`TameArithmetic.lean`.

The local conductor exponent is 0, 1, or 2 for good, multiplicative, or tame
additive reduction. The good sign is 1 and the multiplicative sign is the
negative singular trace, whose equality to the actual finite-field trace was
already proved in `BadPrime.lean`.

At an additive prime p >= 5, the local sign is a Legendre symbol. Negative
j-valuation uses (-1/p). Otherwise, the minimal discriminant valuation modulo
12 selects (-2/p) for residues 3 or 9, (-3/p) for 4 or 8, and (-1/p) for the
other possible additive cases. This is the potentially-good table of
Conrad–Conrad–Helfgott, [Theorem 3.1](https://virtualmath1.stanford.edu/~conrad/papers/rootnumberfinal.pdf),
together with their potentially-multiplicative formula. The conductor formula
is the tame specialization of Tate's algorithm: John Tate, *Algorithm for
determining the type of a singular fiber in an elliptic pencil*, Modular
Functions of One Variable IV (1975), pp. 33–52,
[DOI](https://doi.org/10.1007/BFb0097582).

`potentiallyMultiplicative` explicitly checks c4 != 0. This prevents the j=0
case from accidentally using Nat.factorization's conventional valuation 0 for
the zero integer.

## What Lean proves, and what is assumed

Lean proves the finite square search equivalent to IsSquare in ZMod p, the
executable Legendre symbol equal to mathlib's legendreSym, and the valuation
tests equal to mathematical factorization valuations. It proves the local
conductor/root records agree with these mathematical formulas. Product
correctness, including equivalence of the fast global products to the
mathematical products over all discriminant prime factors, is also proved.
These proofs use only the standard Lean/mathlib axioms.

The identification of the mathematical local formulas with the modular form's
level and Fricke sign is **assumed**, not proved geometric conductor or local
epsilon-factor theory. `Assumptions/FullModularityStatement.lean` makes that
boundary explicit in `ArithmeticModularRealization.tameLevel_eq` and
`tameSign_eq`. As authorized by the user, the existing single axiom
`ellipticModularity` now asserts this stronger general-modularity package.
Its content has changed; retaining the same axiom name does not mean that its
old and new propositions are identical. Both compatibility fields require
proved global minimality and absence of wild additive reduction. They mention
mathematical products, never supplied conductor/sign values or LMFDB answers.

`certifyTameCentralModel` connects checked minimality witnesses and product
equalities to the existing proved central evaluator. Analytic rank-zero
certificates remain conditional on that explicitly stated axiom. Numerical
correctness, nonvanishing, and actual coefficient-prefix identification are
proved, not assumed. No BSD, rank oracle, exact-zero tolerance, or expected
rank enters certificate generation.

## Replay and caching

The batch producer handles semistable curves as before and additionally tries
tame additive curves with a valid minimality witness. The list of candidate
primes may be suggested by the input conductor, but a certificate separately
checks the *complete mathematical discriminant product* in Lean. A wrong or
incomplete hint cannot authorize a conductor or sign.

Run `lake exe certify-batch` to regenerate candidates, kernel-check modules,
and install the sound cache registry. `--seal-cache` revalidates saved source
hashes and rebuilds the full theorem dependency graph; changing the assumption
statement therefore forces dependent certificates to rebuild. The strict
regression still fails if any input is inconclusive.

`AuditTame.lean` guards axiom dependencies. `TameExamples.lean` checks j=0,
all seven potentially-good valuation classes, negative j-valuation, composite
rejection and wild-additive rejection. `certificates/Tame.lean` executes the
cached exact rank-zero value for 49.a1.

Remaining arithmetic work includes wild additive conductor/root formulas at
2 and 3 and the unresolved minimal models. `TameNegativeSign.lean` also connects a checked negative tame sign to exact
central vanishing and the conditional lower bound rank >= 1. Negative signs
require derivative certificates to establish an exact rank; they are never
inserted into the exact-rank registry as rank-one results.

## Checked run (2026-11-18)

The installed rank-zero registry has 468 entries, including 71 new tame additive
curves. The 1,100-curve regression gives 468 matches, zero mismatches and 632
inconclusive inputs. Separate negative-sign replay checks 139 rank >= 1
certificates, including 17 new tame additive cases. Exact rank remains
inconclusive for these lower-bound cases. The cached registry re-seal took
10,515 ms and reproduced the same regression results. The strict regression
exits 1 for incomplete coverage; it does not declare the remaining inputs a
successful complete check.

## Subsequent wild extension

The tame route retains its original scope. The separate
[WILD_ARITHMETIC.md](WILD_ARITHMETIC.md) route now handles additive reduction at
2 and 3 through validated Tate transcripts and mathematical Halberstadt tables.
The earlier remaining-work statements above describe the tame-only milestone.
