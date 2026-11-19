# Broader arithmetic proof engine

Workflow status (2026-11-19): legacy batch/derivative/conductor generators,
`lmfdb-check`, generated registries and bulk certificate directories described
below have been retired. Their command examples and cache counts are historical,
with implementation preserved in baseline commit `fcdc4f2`. The mathematical
proof engine remains; use [`certify_ec`](CERTIFY_EC.md) for current witness
verification and importable theorem generation.

`EllipticCurve/SemistableArithmetic.lean` proves the complete input-model Euler
coefficient identification for every nonsingular integral equation satisfying

    gcd(discriminant, c4) = 1.

The arithmetic theorems do not use `ellipticModularity`. They replace the older
sufficient prefix criterion, which excluded bad primes and repeated primes
with trace magnitude at most one.

## Proof chain

1. A Bezout identity maps the coprime discriminant/c4 condition into every local
   coefficient ring. In a local ring at least one of these invariants is a unit.
2. Unit discriminant implies minimality by maximality of the discriminant
   valuation; unit c4 implies minimality by the valuation criterion ported from
   TauCeti's MinimalModel/Basic development.
3. Two minimal equations over a discrete valuation ring have a fraction-field
   variable change whose scaling coefficient is a unit. Mathlib's integral
   descent theorem lifts the entire variable change to the valuation ring.
4. Consequently the chosen minimal reduction and the supplied reduction differ
   by an invertible variable change over the residue field. This preserves the
   projective point count, including singular points, and preserves smoothness.
5. `Residue.lean` constructs the completed residue field's explicit isomorphism
   with ZMod p through the ideal quotient and the integer prime ideal.
6. TauCeti's good/bad local-polynomial formulas now apply to the supplied input.
   At good primes the polynomial is `1 - a_p X + p X^2`; at bad multiplicative
   primes it is `1 - a_p X`, with the computed projective-model trace. This
   includes residue characteristics two and three.
7. The proved inverse-polynomial recurrence and global Euler-product extraction
   identify every prime-power coefficient. Multiplicativity then identifies the
   entire executable coefficient table with the actual LFunction coefficients.

The principal results are `semistable_localPolynomial`, `semistable_primePower`
and `semistable_prefix`. Their only axioms are the standard Lean/mathlib
foundations: propext, Classical.choice and Quot.sound.

## Batch use

`Assumptions/Batch.lean` exposes `certifySemistableCentralModel`, which combines
this arithmetic with the existing modular realization and central interval
proof. Its modularity dependency remains exactly the previously authorized
single axiom. There is no prefix-eligibility argument.

`lake exe certify-batch` now searches all term limits for supported semistable
models, including prefixes containing bad primes. Each emitted certificate
checks the model condition, conductor, root number and complete numerical
payload before obtaining its exact rank-zero theorem.

## Scope

This engine identifies local factors from an already semistable integral model.
It also provides generic unit-discriminant minimality and minimal-model
comparison lemmas for further extensions. It does not yet minimize arbitrary
additive input equations, identify additive conductors/root numbers with the
modular realization, or evaluate derivatives. Those remain explicit limits.

## Verification

`ArithmeticExamples.lean` checks an actual coefficient at a bad characteristic-
two prime (14.a4, a_4=1), and a good characteristic-two prime with small trace
(17.a2, a_4=-1). Neither example depends on modularity. `AuditArithmetic.lean`
guards the new arithmetic dependency boundary. Existing integration and
conditional audits check the analytic/certificate boundaries separately.

## Verified batch result

The broader engine produced and kernel-checked 70 exact rank-zero certificates
for the 100-curve fixture, with 0 mismatches and 30 inconclusive cases. All 52
cases previously blocked by the prefix shortcut now pass. The remaining
statuses are 26 outside the semistable route, 2 nonpositive sign hints and 2
bad-prime resource limits. The registry proof also passed. The arithmetic
proofs have no custom axioms; the analytic rank certificates retain exactly
the unchanged ellipticModularity dependency. The strict regression still exits
1 because coverage is incomplete.

Validation completed: full default build; all four audits (arithmetic,
integration, conditional and default); the characteristic-two source examples;
fresh bad-prime certificate replay; cached 70-certificate consumer; and fresh
and compiled cubic certificate replays all passed. All eleven port hashes were
verified. The conditional batch's strict exit code remains 1 for its 30
inconclusive inputs.

## Additive extension

The subsequent [additive arithmetic engine](ADDITIVE_REDUCTION.md) now proves
minimality, actual local factors and all coefficient prefixes for all 26 fixture
equations outside the semistable criterion. It includes a stronger 2-adic c4
criterion for 32.a4. These results are unconditional arithmetic; the analytic
rank registry remains at 70 until additive conductor and sign compatibility is
supplied.
