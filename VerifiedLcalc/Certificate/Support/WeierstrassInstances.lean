module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! Serialization and equality instances shared by certificate payloads and the
arithmetic implementation. -/

@[expose] public section

deriving instance Repr, DecidableEq for WeierstrassCurve
