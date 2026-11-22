module

public import VerifiedLcalc.Tactic.CertifyEC

/-!
# Two-factor rational torsion for LMFDB 120.b4

The equation, torsion structure and coordinates come from the checked-in
`data/lmfdb/raw/curvedata-first-1200.txt` snapshot.
-/

@[expose] public section

certify_ec C120b4 from_json "../../fixtures/torsion/120.b4.json"
