# Explicit assumptions

Keep one file per assumption family. The project has two temporary axioms and
a separate family of explicit numerical hypotheses.

- [Elliptic modularity](Modularity.lean) declares `ellipticModularity`. For
  every nonsingular integral Weierstrass equation, it provides an
  [arithmetic modular realization](../EllipticCurve/Modularity/ArithmeticRealization.lean)
  with coefficient and Fricke-sign matching. Its conductor and root-number
  compatibility includes semistable, tame and wild reduction under the fields'
  stated minimality and transcript hypotheses. The geometric Tate/Ogg and
  Halberstadt local compatibility is part of this assumption. Numerical
  correctness and exact vanishing require separate proofs.
- [Low-rank BSD](LowRankBSD.lean) declares
  `analyticOrder_le_one_implies_finrank`. Given the same nonsingular equation,
  an explicit arithmetic modular realization and exact analytic order
  `r ≤ 1` for its L-function at `1`, it gives rational Mordell–Weil rank
  `r`. The axiom covers the forward implication at orders zero and one.
  The converse, higher ranks and the leading-coefficient formula are outside
  its scope.
- [Precision](Precision.lean) imports the
  [curve-specific hypothesis records](../Certificate/Witnesses/Assumptions.lean).
  These are explicit parameters. A nonzero derivative must have a coordinate
  at least the specified gap, and the numerical cutoff must lie strictly
  below that gap. An application requires proved enclosures for the relevant
  derivatives. Exact rank also requires nonvanishing of the next derivative.
  The [Mellin log-moment identity](../Numerics/MellinLogMoments.lean) and the
  [second central derivative formula](../EllipticCurve/Modularity/SecondDerivative.lean)
  give exact integral expressions. Rigorous numerical evaluators for
  derivative orders two and above are still missing.

The default [VerifiedLcalc import](../../VerifiedLcalc.lean) activates neither
temporary axiom. The [`certify_ec` command](../Tactic/CertifyEC.lean) imports
modularity for its canonical analytic realization. The command audits every
emitted theorem according to its checked component. Finite arithmetic and
numerical conclusions use only the standard Lean axioms. The designated
modularity-dependent conclusions may also use `ellipticModularity`.
Low-rank BSD remains opt-in even when using `certify_ec`. The
[opt-in verification module](../Verification/LowRankBSD.lean) applies the
axiom to the explicit realization carried by the conditional analytic proof.

Run `make test-lean` to build the libraries and replay the audits. The
[default audit](../../tests/audits/Audit.lean),
[modularity audit](../../tests/audits/AuditAssumptions.lean), and
[low-rank BSD audit](../../tests/audits/AuditLowRankBSD.lean) check the separate
theorem dependencies. The
[default-import regression](../../tests/consumers/LowRankBSDDefaultAbsent.lean)
checks that the low-rank axiom and its verification lemmas are absent.

The ordinary precision policy is in [Precision.lean](../Precision.lean).
Canonical modular witnesses and analytic proofs live in
[EllipticCurve/Modularity](../EllipticCurve/Modularity). Certificate and
conditional precision-upgrade proofs live in [Verification](../Verification).
A downstream project postulating a gap should name it in an explicitly
imported file and document the curve, precision, function normalization and
derivative prefix.
