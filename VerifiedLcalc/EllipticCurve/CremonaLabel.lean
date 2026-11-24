/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

/-! # Cremona label formatting for singleton orderings -/

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- A conductor with one rational isogeny class has only the class letter `a`. -/
def cremonaSingletonClassLabel (conductor : Nat) : String :=
  String.ofList (Nat.toDigits 10 conductor ++ ['a'])

/-- The only rational isomorphism class in the only isogeny class has suffix `a1`. -/
def cremonaSingletonCurveLabel (conductor : Nat) : String :=
  String.ofList (Nat.toDigits 10 conductor ++ ['a', '1'])

/-- The class label concatenates the decimal conductor and the singleton letter. -/
theorem cremonaSingletonClassLabel_eq (conductor : Nat) :
    cremonaSingletonClassLabel conductor = toString conductor ++ "a" := by
  rw [cremonaSingletonClassLabel, String.ofList_append, Nat.toString_eq_ofList_toDigits]

/-- The curve label concatenates the decimal conductor and its singleton suffix. -/
theorem cremonaSingletonCurveLabel_eq (conductor : Nat) :
    cremonaSingletonCurveLabel conductor = toString conductor ++ "a1" := by
  rw [cremonaSingletonCurveLabel, String.ofList_append, Nat.toString_eq_ofList_toDigits]

end VerifiedLcalc.EllipticCurve
