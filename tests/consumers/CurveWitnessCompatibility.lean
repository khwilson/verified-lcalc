import VerifiedLcalc.Certificate.EllipticWitness

/-! The historical singular import still exposes the moved public witness names. -/

open VerifiedLcalc

example {R : Type} [CommRing R] (curve : WeierstrassCurve R) : Type := EllipticProofs curve
example {R : Type} [CommRing R] : Type := DiscriminantWitness R
example : Type := AbcQualityClaim
