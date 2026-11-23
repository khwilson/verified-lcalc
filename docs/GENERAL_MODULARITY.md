# General modularity and arithmetic compatibility

The assumption is general elliptic modularity for E/Q, including curves with
additive reduction. The user clarified this authorization on 2026-11-18. It is
not limited to the semistable modularity sufficient for FLT. No further approval
is needed merely to use general modularity for additive curves.

The base `EllipticModularity` proposition has the shape

```lean
∀ equation : Artifacts.CurveEquation, discriminant equation ≠ 0 →
  Nonempty (ModularRealization equation)
```

There is no semistability hypothesis. A realization contains a normalized
weight-two cusp form, all actual curve Euler coefficients, and Fricke symmetry.
Mathlib proves that the associated continued L-function is entire. The original finite formulas for its
level and sign were semistable specializations. Those formulas were previously
conflated with the scope of the modularity assumption; that distinction is now
explicit in AGENTS.md and the certificate interfaces.

## Witness-independent certification

`Assumptions/RealizationIndependence.lean` proves that any two realizations of
the same curve have the same entire L-function. Both agree with the actual
Dirichlet series on Re(s)>2. The complex identity theorem then gives equality
everywhere, and hence equality of analytic orders at every point. This proof
uses only the standard Lean/mathlib axioms, with the realizations as inputs.
It requires neither semistability nor equality of the two levels/signs.

`Assumptions/GeneralCertification.lean` provides:

* `ArithmeticCompatibility`: a genuine realization with proofs that its level
  and sign match the computation's inputs. An integer conductor or a database
  sign alone cannot construct this evidence.
* `certifyCentralWithRealization`: numerical central certification against any
  supplied genuine realization, without a semistability hypothesis or custom
  axiom in the implication.
* `certifyGeneralMinimalCentral`: connects a proved minimal input model and
  its coefficient prefix to that realization, then transports the result to
  the canonical curve continuation. It does not require agreement with the
  level/sign of the particular realization selected by Classical.choice.
* `certifyGeneralNegativeLowerBound`: transports exact central vanishing and
  the lower bound rank >= 1 from verified general negative-sign compatibility.
  It does not assert exact rank one.

The semistable arithmetic constructor remains one way to supply compatibility,
not a restriction on the general interface. General arithmetic proofs can
supply another realization directly.

## Validation and remaining work

`tests/VerifiedLcalcTests/Fixtures/GeneralModularityExamples.lean` checks applicability to the
non-semistable curve y^2=x^3+1, independence for any two of its realizations,
and replay of the existing 11.a2 rank-zero and 37.a1 lower-bound certificates
through the unrestricted interfaces. `AuditGeneralModularity.lean` guards the
axiom dependencies separately.

The original interface work added no axiom and did not change the existing
modularity statement. The subsequent tame arithmetic integration **strengthens
the content of the same authorized axiom**: `GeneralEllipticModularity` supplies
an `ArithmeticModularRealization` with standard tame conductor/root-number
compatibility. The old base realization remains the interface for analytic
proofs and witness independence. See [TAME_ARITHMETIC.md](TAME_ARITHMETIC.md)
for the exact assumed fields and the separate axiom-free executable proofs.
The subsequent [wild arithmetic integration](WILD_ARITHMETIC.md) adds explicit Tate/Ogg/Halberstadt compatibility at 2 and 3, again under proved minimality and validated transcripts. Numerical correctness,
exact derivative vanishing, BSD, and expected ranks are not assumed.
