module

public import VerifiedLcalc.Verification.TameNegativeSign
public import VerifiedLcalc.Verification.WildCertification

/-! # Negative root numbers and analytic rank bounds for conductors below 160 -/

@[expose] public section
open VerifiedLcalc.Certification
open VerifiedLcalc
namespace VerifiedLcalcTests.Fixtures.NegativeSigns
open EllipticCurve Modularity
set_option maxRecDepth 100000

namespace C37_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C37_a1

namespace C43_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := 0, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C43_a1

namespace C53_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := 0, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C53_a1

namespace C57_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -2, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C57_a1

namespace C58_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -1, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C58_a1

namespace C61_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -2, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C61_a1

namespace C65_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C65_a1

namespace C65_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 4, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C65_a2

namespace C77_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C77_a1

namespace C79_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := -2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C79_a1

namespace C82_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -12, a₆ := -16 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C82_a1

namespace C82_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C82_a2

namespace C83_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := 1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C83_a1

namespace C88_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -4, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
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
end C88_a1

namespace C89_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 1, a₄ := -1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C89_a1

namespace C91_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_a1

namespace C91_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -117, a₆ := -1245 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_b1

namespace C91_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -7, a₆ := 5 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_b2

namespace C91_b3
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := 13, a₆ := 42 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_b3

namespace C92_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0,
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
end C92_a1

namespace C99_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -17, a₆ := 30 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 11, 11] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 0, starT := 0, cubicRoot := 0,
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
end C99_a1

namespace C99_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 11] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 0, starT := 0, cubicRoot := 0,
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
end C99_a2

namespace C101_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -1, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C101_a1

namespace C102_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C102_a1

namespace C102_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 8, a₆ := 10 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C102_a2

namespace C106_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -7, a₆ := 5 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C106_a1

namespace C112_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -40, a₆ := 84 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1,
    quadraticRoot := 0, chain := [0, 0], kodaira := -7 }
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
end C112_a1

namespace C112_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 0, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1,
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
end C112_a2

namespace C117_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -626, a₆ := 6180 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 0, starT := 1, cubicRoot := 2,
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
end C117_a1

namespace C117_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -176, a₆ := -768 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 0, starT := 1, cubicRoot := 1,
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
end C117_a2

namespace C117_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -41, a₆ := 96 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 0, starT := 1, cubicRoot := 1,
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
end C117_a3

namespace C117_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := 4, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 1, t := 0, starT := 1, cubicRoot := 0,
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
end C117_a4

namespace C118_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := 1, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C118_a1

namespace C121_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -887, a₆ := -10143 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C121_b1

namespace C121_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -7, a₆ := 10 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem tame : tameAtWild equation = true := by decide +kernel
theorem sign_negative : tameSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_tame_negative equation nonsingular witness witness_valid tame sign_negative
end C121_b2

namespace C122_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := 2, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C122_a1

namespace C123_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -10, a₆ := 10 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C123_a1

namespace C123_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := 20, a₆ := -890 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C123_a2

namespace C123_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 1, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C123_b1

namespace C124_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -2, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
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
end C124_a1

namespace C124_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 18, a₆ := -11 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31, 31, 31] }
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
end C124_a2

namespace C128_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -9, a₆ := 7 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1,
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
end C128_a1

namespace C128_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 1, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2] }
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
end C128_a2

namespace C129_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -19, a₆ := 39 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C129_a1

namespace C130_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -208, a₆ := -1122 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a1

namespace C130_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -33, a₆ := 68 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a2

namespace C130_a3
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := -13, a₆ := 156 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a3

namespace C130_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 0, a₃ := 1, a₄ := 112, a₆ := -4194 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a4

namespace C131_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C131_a1

namespace C135_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -3, a₆ := 4 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 5] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0,
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
end C135_a1

namespace C136_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -4, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 17] }
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
end C136_a1

namespace C136_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := 16, a₆ := 16 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
def wildData : WildData := {
  atTwo := some {
    r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0,
    quadraticRoot := 1, chain := [], kodaira := -3 }
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
end C136_a2

namespace C138_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -31, a₆ := 55 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C138_a1

namespace C138_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -1, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C138_a2

namespace C141_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 1, a₄ := -12, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C141_a1

namespace C141_d1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -1, a₆ := 0 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C141_d1

namespace C142_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -1, a₆ := -1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C142_a1

namespace C142_d1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -12, a₆ := 15 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C142_d1

namespace C143_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -1, a₆ := -2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C143_a1

namespace C145_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -3, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C145_a1

namespace C145_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := 2, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C145_a2

namespace C148_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -5, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
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
end C148_a1

namespace C152_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 1, a₃ := 0, a₄ := -1, a₆ := 3 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 19] }
def wildData : WildData := {
  atTwo := some {
    r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1,
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
end C152_a1

namespace C153_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -3, a₆ := 2 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 17] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0,
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
end C153_a1

namespace C153_b1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -534, a₆ := 4752 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 17, 17, 17] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 1, cubicRoot := 1,
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
end C153_b1

namespace C153_b2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 6, a₆ := 27 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
def wildData : WildData := {
  atTwo := none
  atThree := some {
    r := 2, s := 0, t := 1, starT := 1, cubicRoot := 1,
    quadraticRoot := 0, chain := [1, 0], kodaira := -7 } }
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
end C153_b2

namespace C154_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -469, a₆ := 4029 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C154_a1

namespace C154_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 0, a₄ := -29, a₆ := 69 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C154_a2

namespace C155_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -840, a₆ := -9114 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C155_a1

namespace C155_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := 10, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C155_a2

namespace C155_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 1, a₄ := -1, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C155_c1

namespace C156_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -20, a₆ := -24 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13] }
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
end C156_a1

namespace C156_a2
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := -1, a₃ := 0, a₄ := -5, a₆ := 6 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13] }
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
end C156_a2

namespace C158_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := 1, a₃ := 0, a₄ := -3, a₆ := 1 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C158_a1

namespace C158_c1
def equation : (WeierstrassCurve ℤ) := { a₁ := 1, a₂ := -1, a₃ := 1, a₄ := -9, a₆ := 9 }
theorem nonsingular : equation.Δ ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C158_c1

end VerifiedLcalcTests.Fixtures.NegativeSigns
