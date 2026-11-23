module

public import VerifiedLcalc.Verification.TameNegativeSign
public import VerifiedLcalc.Verification.WildCertification

/-! # Negative root numbers and analytic rank bounds for conductors from 160 through 219 -/

@[expose] public section
open VerifiedLcalc.Certification
open VerifiedLcalc
namespace VerifiedLcalcTests.Fixtures.NegativeSigns
open EllipticCurve Modularity
set_option maxRecDepth 100000

namespace C160_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -6, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C160_a1

namespace C160_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -1, a₆ := 15 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1,
    quadraticRoot := 0, chain := [1, 1], kodaira := -7 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C160_a2

namespace C162_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -6, a₆ := 8 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C162_a1

namespace C162_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := 39, a₆ := -19 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 1, t := 1, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C162_a2

namespace C163_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -2, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C163_a1

namespace C166_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -6, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C166_a1

namespace C170_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -8, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C170_b1

namespace C170_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := 12, a₆ := 38 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C170_b2

namespace C171_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -6924, a₆ := 221760 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -1 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C171_b1

namespace C171_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -84, a₆ := 315 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19, 19, 19] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -1 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C171_b2

namespace C171_b3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 6, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -1 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C171_b3

namespace C172_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -13, a₆ := 15 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -4 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C172_a1

namespace C172_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 67, a₆ := 79 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43, 43, 43] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -4 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C172_a2

namespace C175_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -148, a₆ := 748 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C175_a1

namespace C175_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 2, a₆ := -2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C175_a2

namespace C175_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -3283, a₆ := -74657 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C175_b1

namespace C175_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -33, a₆ := 93 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C175_b2

namespace C175_b3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 217, a₆ := -282 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C175_b3

namespace C176_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -77, a₆ := 289 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -1 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C176_a1

namespace C176_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := 3, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -1 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C176_a2

namespace C184_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := 0, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C184_a1

namespace C184_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -4, a₆ := 5 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C184_b1

namespace C185_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -156, a₆ := 700 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_a1

namespace C185_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -5, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_b1

namespace C185_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -4, a₆ := -3 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_c1

namespace C185_c2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := 1, a₆ := -9 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_c2

namespace C189_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -3, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 7] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C189_a1

namespace C189_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -3834, a₆ := -91375 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 0, t := 1, starT := 1, cubicRoot := 1,
    quadraticRoot := 1, chain := [], kodaira := -2 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C189_b1

namespace C189_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -54, a₆ := -88 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 0, t := 1, starT := 1, cubicRoot := 1,
    quadraticRoot := 0, chain := [], kodaira := -4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C189_b2

namespace C189_b3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -24, a₆ := 45 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 7] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 2 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C189_b3

namespace C190_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 2, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C190_a1

namespace C190_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -48, a₆ := 147 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C190_b1

namespace C192_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -129, a₆ := 609 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [0, 1, 1, 0], kodaira := -9 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C192_a1

namespace C192_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -9, a₆ := 9 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [0], kodaira := -6 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C192_a2

namespace C192_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -4, a₆ := -2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 2 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C192_a3

namespace C192_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := 31, a₆ := 33 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness :=
  { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [0, 0, 1, 0], kodaira := -9 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C192_a4

namespace C196_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -142, a₆ := 701 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 4 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C196_a1

namespace C196_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -2, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 4 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C196_a2

namespace C197_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -5, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C197_a1

namespace C198_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -3168, a₆ := 69430 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 11] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 2, starT := 2, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C198_a1

namespace C198_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -198, a₆ := 1120 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 2, starT := 2, cubicRoot := 0,
    quadraticRoot := 0, chain := [2], kodaira := -6 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C198_a2

namespace C198_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -108, a₆ := 2074 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 2, starT := 2, cubicRoot := 1,
    quadraticRoot := 0, chain := [0, 0, 1], kodaira := -8 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C198_a3

namespace C198_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -18, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 11] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 2, starT := 2, cubicRoot := 2,
    quadraticRoot := 0, chain := [], kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C198_a4

namespace C200_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -28, a₆ := 48 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1,
    quadraticRoot := 0, chain := [], kodaira := -5 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C200_b1

namespace C200_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -3, a₆ := -2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C200_b2

namespace C201_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C201_a1

namespace C201_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C201_b1

namespace C201_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -794, a₆ := 8289 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C201_c1

namespace C203_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := 0, a₆ := -2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C203_b1

namespace C205_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -232, a₆ := -1286 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a1

namespace C205_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -27, a₆ := 26 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a2

namespace C205_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -22, a₆ := 44 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a3

namespace C205_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := 98, a₆ := 126 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a4

namespace C207_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -140, a₆ := 668 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 23, 23] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 1, t := 1, starT := 1, cubicRoot := 2,
    quadraticRoot := 0, chain := [], kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C207_a1

namespace C207_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -5, a₆ := 20 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 23] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 1, t := 1, starT := 1, cubicRoot := 2,
    quadraticRoot := 0, chain := [0], kodaira := -6 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C207_a2

namespace C208_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -16, a₆ := 32 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [0, 1], kodaira := -7 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C208_b1

namespace C209_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -27, a₆ := 55 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C209_a1

namespace C209_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := 193, a₆ := -308 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C209_a2

namespace C210_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -373, a₆ := 2623 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a1

namespace C210_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -23, a₆ := 33 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a2

namespace C210_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -3, a₆ := -3 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a3

namespace C210_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 7, a₆ := 147 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a4

namespace C212_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -4, a₆ := 8 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 53] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1,
    quadraticRoot := 0, chain := [], kodaira := -4 }
  atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C212_a1

namespace C214_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := 1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C214_a1

namespace C214_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -193, a₆ := 1012 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C214_b1

namespace C214_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -12, a₆ := 16 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C214_c1

namespace C215_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -8, a₆ := -12 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C215_a1

namespace C216_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -12, a₆ := 20 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1,
    quadraticRoot := 0, chain := [], kodaira := -5 }
  atThree := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData
    wild_valid sign_negative
end C216_a1

namespace C218_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -2, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C218_a1

namespace C218_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 18, a₆ := -104 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C218_a2

namespace C219_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -6, a₆ := 8 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_a1

namespace C219_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -27, a₆ := -85 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_b1

namespace C219_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := 3, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_b2

namespace C219_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -1297, a₆ := -18530 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_c1

namespace C219_c2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -82, a₆ := -305 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_c2

end VerifiedLcalcTests.Fixtures.NegativeSigns
