# Authorized refinement of the temporary modularity axiom

The original axiom gave a modular realization at an existential level and sign.
It did not state that these agree with the conductor and sign computed from an
integral model. That missing compatibility cannot be replaced by reading the
LMFDB values.

For the first example, the user-authorized refinement adds the following
standard semistable compatibility to the same modularity axiom:

For any integral nonsingular Weierstrass model with

    gcd(discriminant, c4) = 1,

choose the modular realization so that

    level = product of the distinct prime divisors of |discriminant|
    rootNumber = - product_{p divides discriminant} (-frobeniusTrace(model,p)).

Here the trace at a singular prime counts all affine equation solutions plus
infinity. Under the coprimality condition all bad reduction is multiplicative,
and the trace is +1 or -1. The initial minus sign is the real-place factor.

These are established general conductor/root-number compatibility facts. They
are new **assumed** fields of our formal modularity package,
not new proved theorems. They do not assume any numerical interval, expected
rank, derivative evaluation, BSD, or cutoff-based exact vanishing.

For 11.a2 the coprimality condition is an exact finite check. The discriminant
is -11^5 and the singular trace at 11 is +1; the displayed formulas therefore
give level 11 and sign +1. Their integer computations can be kernel-checked,
while the compatibility with the modular realization remains explicitly
dependent on the refined axiom.

The user explicitly approved this expansion on 2026-11-17. It is now active as
`ModularRealization.semistableLevel_eq` and `semistableSign_eq`, within the same
single axiom `ellipticModularity`. No additional custom axiom was introduced.
The arithmetic identities for 11.a2 and 37.a1 are separately kernel-checked.
