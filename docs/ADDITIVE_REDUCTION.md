# Additive reduction arithmetic

The arithmetic backend now supports all 26 equations in the 100-curve fixture
that failed the semistable criterion. This is coefficient support, not 26 new
analytic-rank certificates. The certified rank registry remains at 70.

## Proof chain

`MinimalArithmetic.lean` identifies the actual local Euler polynomial from any
supplied integral equation proved minimal at the relevant prime. It then
identifies every prime-power coefficient and the complete executable coefficient
prefix with mathlib/Tau Ceti's actual curve L-function coefficients. The earlier
semistable API now uses this general local comparison.

`ReductionCore.lean` contains executable reduction classification, two sufficient
minimality criteria, a finite factorization witness, and checked witness search.
Its imports stay free of analytic mathlib modules. A witness lists prime factors
of the discriminant with repetition; the kernel checks primality, their product,
and a minimality criterion at each listed prime. Missing or incorrect factors
cannot be accepted. The conductor from the fixture is used only to propose
candidate factors; its mathematical correctness is not assumed.

`AdditiveArithmetic.lean` proves the discriminant criterion: if p^12 does not
divide Delta, the integral equation is minimal at p. It connects the additive
classification to vanishing Delta and c4 in the residue field, proves zero
Frobenius trace, and proves that the actual local Euler polynomial is exactly 1.
This works in characteristics 2 and 3 as well as larger characteristics.

`TwoAdicMinimality.lean` handles the remaining equation 32.a4. An integral
Weierstrass equation over the 2-adic integers has c4 either a unit or divisible
by 16. If the input c4 has valuation six, a nonintegral scaling would leave an
integral equation with c4 valuation two, contradicting that invariant identity.
For 32.a4, Delta=-4096 and c4=-192. The discriminant-only criterion is
inconclusive; the stronger criterion proves minimality.

`ReductionArithmetic.lean` proves both executable criteria sound and converts a
validated finite factorization witness into minimality at every prime. Primes
outside the factorization are covered by the discriminant criterion.

`AdditiveExamples.lean` contains generated, kernel-checked witnesses, full prefix
correctness theorems, and additive Euler polynomial equalities for all 26 curves.
These proofs require no modularity axiom. `ReductionExamples.lean` also checks
that the stronger criterion is necessary for 32.a4, rejects a scaled equation,
and proves the actual coefficient a_4=0 for 32.a4.

## Historical reproduction and cache

These producer and audit commands refer to the `fcdc4f2` baseline. In the
current checkout, `make test-lean` builds and runs the
[compiled additive consumer](../tests/consumers/Additive.lean).

```sh
lake exe additive-witnesses --check
lake env lean AuditAdditive.lean
lake env lean tests/consumers/Additive.lean
```

The producer reads only curve inputs, never reference ranks. It writes proposals
to `output/additive/proposals.tsv`. With `--check`, it builds the generated Lean
module and only on success writes `output/additive/checked.tsv`; the build output
is saved in `output/additive/kernel-replay.log`. The checked source digest is
recorded in `output/additive/checked-source.sha256`; a changed source or new
check invalidates the previous checked report before replay. Strict checking fails if any
selected equation remains unsupported or replay fails. The source is rewritten
only when its content changes, and Lake caches its checked `.olean` artifact.
The cached consumer imports those proofs without recomputing their witnesses.

`AuditAdditive.lean` guards the axiom dependencies of the engine and all 26 prefix
theorems: only propext, Classical.choice, and Quot.sound are permitted.

## Analytic-rank boundary

`certifyMinimalCentralModel` in `Assumptions/Batch.lean` connects general minimal
models to the existing central evaluator. It still requires proofs that the
modular realization's level and Fricke sign equal the proposed conductor and
root number. Those equalities are not supplied by fixture metadata.

General modularity is authorized for every elliptic curve over Q, including
additive reduction (clarified 2026-11-18). The existing existence axiom already
quantifies over all nonsingular equations. The currently implemented finite
conductor/sign formulas are semistable arithmetic specializations; that is a
limitation of the arithmetic implementation, not the scope of modularity.

Additive Euler factors do not determine conductor exponents or local root
numbers; particularly at 2 and 3, wild ramification matters. The local arithmetic
that computes these inputs still needs correctness evidence. No further
permission is needed merely to use general modularity. See
[GENERAL_MODULARITY.md](GENERAL_MODULARITY.md) for witness-independent general
certification. This implementation is not a complete Tate algorithm or minimizer.

## Validation of this implementation

The full default build and the opt-in generated rank registry build passed.
All five audits passed: `AuditAdditive.lean`, `AuditArithmetic.lean`,
`AuditIntegration.lean`, `AuditAssumptions.lean`, and `Audit.lean`. Fresh Cubic
and reduction-example source replay, the compiled Cubic consumer, and the
compiled additive consumer also passed. The latter imports the proof of
32.a4's a_4=0 and executes its coefficient prefix as
`[1, 0, 0, 0, -2, 0, 0, 0]`.
