/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import VerifiedLcalc.EllipticCurve.Tate.Tamagawa

/-! # The intrinsic Tamagawa product of 37.a1

The model has discriminant 37. Its completed local factor is one at the single
multiplicative place of index one and at all places of good reduction.
-/

@[expose] public section

namespace Curve37a1Tamagawa

open VerifiedLcalc VerifiedLcalc.EllipticCurve WeierstrassCurve
open IsDedekindDomain WithZero
open scoped WithZero

/-- The integral equation of 37.a1. -/
def model : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

instance : (model.baseChange ℚ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- Every completed local factor equals one, so the intrinsic product is one. -/
theorem product_eq_one : (model.baseChange ℚ).tamagawaProduct (R := ℤ) = 1 := by
  apply tamagawaProduct_eq_one_of_supported_primes model [37]
  · intro p hp hd
    have h : p = 37 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37)).mp
      (by change (p : ℤ) ∣ 37 at hd; exact_mod_cast hd)
    simp [h]
  · decide

/-- The explicit proof attached to the raw Tamagawa product report. -/
def product : TamagawaProductFact model := ⟨1, product_eq_one⟩

certify_ec TamagawaCertificate from
  { equation := model, tamagawaProduct := some 1 }
  with_proofs { tamagawaProduct := some product }

end Curve37a1Tamagawa
