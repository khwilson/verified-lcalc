import VerifiedLcalc.Verification.CurveData

/-!
# Generic multiplicative and additive order checks

The multiplicative checker is the source for the generated additive API used by
the elliptic torsion certificate. These small finite examples exercise both.
-/

open VerifiedLcalc

example : EllipticWitness.exactOrderCheckMul (2 : ZMod 5) 4 = true := by decide +kernel

example : orderOf (2 : ZMod 5) = 4 :=
  EllipticWitness.exactOrderCheckMul_sound (by decide +kernel)

example : EllipticWitness.exactOrderCheckMul (2 : ZMod 5) 2 = false := by decide +kernel

example : EllipticWitness.exactOrderCheck (1 : ZMod 5) 5 = true := by decide +kernel

example : addOrderOf (1 : ZMod 5) = 5 :=
  EllipticWitness.exactOrderCheck_sound (by decide +kernel)

example : EllipticWitness.exactOrderCheck (1 : ZMod 5) 4 = false := by decide +kernel

example {A : Type*} [Monoid A] [DecidableEq A] {P : A} {n : Nat}
    (h : EllipticWitness.exactOrderCheckMul P n = true) : orderOf P = n :=
  EllipticWitness.exactOrderCheckMul_sound h

example {A : Type*} [AddMonoid A] [DecidableEq A] {P : A} {n : Nat}
    (h : EllipticWitness.exactOrderCheck P n = true) : addOrderOf P = n :=
  EllipticWitness.exactOrderCheck_sound h
