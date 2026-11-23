/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.EllipticCertificate
public import VerifiedLcalc.Certificate.Witnesses.EllipticWitness

/-! # Ordinary witness structures for elliptic-curve certificates

Import this module for the ordinary records used by `certify_ec`. For a specific subject,
choose a module under `VerifiedLcalc.Certificate.Witnesses`.

* `InputData` defines shared claims, transcripts, numerical payloads, and point evidence.
  `ArtifactData` defines requests and recorded derivative boxes.
* `Invariants` covers Weierstrass invariants, abc quality, and conductor and root number
  compatibility. `FinitePrimes` covers local reduction, minimal models, and coefficients.
* `Algebraic` covers points, Mordell–Weil bounds, the regulator, torsion, and isogenies.
  `Analytic` covers finite checks, analytic enclosures, special values, and rank.
* `EllipticWitness` defines the command input. `EllipticCertificate` defines the optional Lean
  proof attachments and the checked result available as `Name.certificate`.

Import `VerifiedLcalc.Certificate.Witnesses.Assumptions` explicitly for evidence stated in
terms of the canonical realization supplied by the modularity assumption.
-/
