module

public import VerifiedLcalc.Verification.TameNegativeSign
public import VerifiedLcalc.Verification.WildCertification

/-! # Negative root numbers and analytic rank bounds for conductors at least 220 -/

@[expose] public section
open VerifiedLcalc.Certification
open VerifiedLcalc
namespace VerifiedLcalcTests.Fixtures.NegativeSigns
open EllipticCurve Modularity
set_option maxRecDepth 100000

namespace C220_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -7100, a₆ := -232652 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 11, 11, 11] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0,
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
end C220_a1

namespace C220_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -445, a₆ := -3720 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 11, 11, 11, 11, 11, 11] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0,
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
end C220_a2

namespace C220_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -100, a₆ := -252 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 11] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0,
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
end C220_a3

namespace C220_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -45, a₆ := 100 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 11, 11] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0,
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
end C220_a4

namespace C224_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -8, a₆ := -8 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
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
end C224_a1

namespace C224_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7] }
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
end C224_a2

namespace C225_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -75, a₆ := 256 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 0, t := 1, starT := 1, cubicRoot := 1,
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
end C225_a1

namespace C225_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 375, a₆ := -12344 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness :=
  { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 0, t := 1, starT := 1, cubicRoot := 0,
    quadraticRoot := 0, chain := [1, 2, 1, 0], kodaira := -9 } }
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
end C225_a2

namespace C225_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 0, a₆ := -34 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 0, t := 1, starT := 1, cubicRoot := 2,
    quadraticRoot := 1, chain := [], kodaira := -3 } }
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
end C225_c1

namespace C225_c2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 0, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 5, 5] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 } }
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
end C225_c2

namespace C226_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -45, a₆ := -119 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C226_a1

namespace C226_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -5, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C226_a2

namespace C228_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := 3, a₆ := 9 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 19] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1,
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
end C228_a1

namespace C229_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -2, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C229_a1

namespace C232_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := 8, a₆ := -4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 29] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1,
    quadraticRoot := 0, chain := [], kodaira := -3 }
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
end C232_a1

namespace C234_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -63, a₆ := 209 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 13, 13] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 } }
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
end C234_a1

namespace C234_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -3, a₆ := 5 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 13] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 3 } }
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
end C234_a2

namespace C235_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := -5, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C235_b1

namespace C236_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -1, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 59] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0,
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
end C236_a1

namespace C238_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -8, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_a1

namespace C238_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := 2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_a2

namespace C238_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -700, a₆ := 7056 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_c1

namespace C238_c2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -60, a₆ := 16 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_c2

namespace C240_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -216, a₆ := 1296 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [1, 0], kodaira := -7 }
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
end C240_a1

namespace C240_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -136, a₆ := -560 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [1, 0], kodaira := -7 }
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
end C240_a2

namespace C240_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -16, a₆ := 16 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [1], kodaira := -6 }
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
end C240_a3

namespace C240_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := 4, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
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
end C240_a4

namespace C242_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -52, a₆ := 144 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C242_b1

namespace C242_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 3, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C242_b2

namespace C243_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 0, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0,
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
end C243_a1

namespace C243_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 0, a₆ := 20 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 0, t := 1, starT := 1, cubicRoot := 0,
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
end C243_a2

namespace C244_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 1, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 61] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1,
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
end C244_a1

namespace C245_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -7, a₆ := 12 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C245_a1

namespace C245_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -6435, a₆ := 210006 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C245_c1

namespace C245_c2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -65, a₆ := -204 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C245_c2

namespace C245_c3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 425, a₆ := 433 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C245_c3

namespace C246_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -66, a₆ := 180 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C246_a1

namespace C246_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -26, a₆ := 444 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C246_a2

namespace C248_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 0, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
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
end C248_a1

namespace C248_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 1, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0,
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
end C248_c1

namespace C249_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := -55, a₆ := 134 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C249_a1

namespace C249_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 2, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C249_b1

namespace C252_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -327, a₆ := 2270 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1,
    quadraticRoot := 0, chain := [], kodaira := -4 }
  atThree := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0,
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
end C252_a1

namespace C252_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -12, a₆ := 65 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0,
    quadraticRoot := 0, chain := [], kodaira := 4 }
  atThree := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 2,
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
end C252_a2

namespace C254_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -5, a₆ := -3 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_a1

namespace C254_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -24432, a₆ := -1471934 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_b1

namespace C254_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -302, a₆ := -2036 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_b2

namespace C254_b3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -22, a₆ := 36 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_b3

namespace C256_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -3, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0,
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
end C256_a2

namespace C256_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0,
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
end C256_b1

namespace C258_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 3, a₆ := -3 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C258_b1

namespace C258_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -15, a₆ := 22 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C258_c1

namespace C262_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -2, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C262_a1

namespace C262_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 1, a₆ := 25 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C262_b1

namespace C265_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -138, a₆ := 656 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C265_a1

namespace C265_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -133, a₆ := 702 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C265_a2

namespace C269_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -2, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C269_a1

namespace C272_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -48, a₆ := -140 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1,
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
end C272_a1

namespace C272_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -8, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1,
    quadraticRoot := 0, chain := [1], kodaira := -6 }
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
end C272_a2

namespace C273_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -26, a₆ := 68 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C273_a1

namespace C274_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -2846, a₆ := 59156 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_a1

namespace C274_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_b1

namespace C274_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := 8, a₆ := -6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_b2

namespace C274_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -7, a₆ := 9 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_c1

namespace C275_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -1480, a₆ := 22272 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C275_a1

namespace C275_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -730, a₆ := -7228 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C275_a2

namespace C275_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -105, a₆ := 272 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C275_a3

namespace C275_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := 20, a₆ := 22 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C275_a4

namespace C277_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := 0, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C277_a1

namespace C278_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 9 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C278_b1

namespace C280_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -412, a₆ := 3316 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 7, 7, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1,
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
end C280_a1

namespace C280_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -1, a₆ := 5 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0,
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
end C280_b1

namespace C282_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := -255, a₆ := 1461 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C282_a1

namespace C282_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := -15, a₆ := 21 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C282_a2

namespace C285_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -76, a₆ := -19 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_a1

namespace C285_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 19, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_a2

namespace C285_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -93, a₆ := -378 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_b1

namespace C285_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 2, a₆ := -17 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_b2

namespace C5077_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -7, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C5077_a1

end VerifiedLcalcTests.Fixtures.NegativeSigns
