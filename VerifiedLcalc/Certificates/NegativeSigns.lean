module

public import VerifiedLcalc.Assumptions.TameNegativeSign
public import VerifiedLcalc.Assumptions.WildCertification

@[expose] public section
namespace VerifiedLcalc.Certificates.NegativeSigns
open EllipticCurve Assumptions
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace C101_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C101_a1

namespace C102_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C102_a1

namespace C102_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 8, a6 := 10 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C102_a2

namespace C106_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -7, a6 := 5 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C106_a1

namespace C112_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -40, a6 := 84 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
def wildData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0],              kodaira := -7 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C112_a1

namespace C112_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C112_a2

namespace C117_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -626, a6 := 6180 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C117_a1

namespace C117_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -176, a6 := -768 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C117_a2

namespace C117_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -41, a6 := 96 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C117_a3

namespace C117_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C117_a4

namespace C118_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 1, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C118_a1

namespace C121_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -887, a6 := -10143 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -7, a6 := 10 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C122_a1

namespace C123_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -10, a6 := 10 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C123_a1

namespace C123_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 20, a6 := -890 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C123_a2

namespace C123_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 1, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C123_b1

namespace C124_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C124_a1

namespace C124_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 18, a6 := -11 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31, 31, 31] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C124_a2

namespace C128_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := 7 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C128_a1

namespace C128_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C128_a2

namespace C129_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -19, a6 := 39 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C129_a1

namespace C130_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -208, a6 := -1122 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a1

namespace C130_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -33, a6 := 68 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a2

namespace C130_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -13, a6 := 156 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a3

namespace C130_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 112, a6 := -4194 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C130_a4

namespace C131_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C131_a1

namespace C135_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 5] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C135_a1

namespace C136_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 17] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C136_a1

namespace C136_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 16 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C136_a2

namespace C138_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -31, a6 := 55 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C138_a1

namespace C138_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C138_a2

namespace C141_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -12, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C141_a1

namespace C141_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C141_d1

namespace C142_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C142_a1

namespace C142_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -12, a6 := 15 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C142_d1

namespace C143_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := -2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C143_a1

namespace C145_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C145_a1

namespace C145_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 2, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C145_a2

namespace C148_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C148_a1

namespace C152_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 3 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 19] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C152_a1

namespace C153_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 17] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C153_a1

namespace C153_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -534, a6 := 4752 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 17, 17, 17] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C153_b1

namespace C153_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 27 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 0],                kodaira := -7 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C153_b2

namespace C154_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -469, a6 := 4029 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C154_a1

namespace C154_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -29, a6 := 69 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C154_a2

namespace C155_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -840, a6 := -9114 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C155_a1

namespace C155_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 10, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C155_a2

namespace C155_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C155_c1

namespace C156_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := -24 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C156_a1

namespace C156_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C156_a2

namespace C158_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -3, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C158_a1

namespace C158_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -9, a6 := 9 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C158_c1

namespace C160_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -6, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C160_a1

namespace C160_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 15 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
def wildData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C160_a2

namespace C162_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := 8 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C162_a1

namespace C162_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 39, a6 := -19 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C162_a2

namespace C163_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -2, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C163_a1

namespace C166_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -6, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C166_a1

namespace C170_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -8, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C170_b1

namespace C170_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 12, a6 := 38 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C170_b2

namespace C171_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -6924, a6 := 221760 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C171_b1

namespace C171_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -84, a6 := 315 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19, 19, 19] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C171_b2

namespace C171_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C171_b3

namespace C172_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := 15 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C172_a1

namespace C172_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 67, a6 := 79 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43, 43, 43] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C172_a2

namespace C175_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -148, a6 := 748 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 2, a6 := -2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3283, a6 := -74657 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -33, a6 := 93 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 217, a6 := -282 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -77, a6 := 289 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C176_a1

namespace C176_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C176_a2

namespace C184_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C184_a1

namespace C184_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 5 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C184_b1

namespace C185_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -156, a6 := 700 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_a1

namespace C185_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -5, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_b1

namespace C185_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -4, a6 := -3 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_c1

namespace C185_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := -9 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C185_c2

namespace C189_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 7] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C189_a1

namespace C189_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3834, a6 := -91375 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C189_b1

namespace C189_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -54, a6 := -88 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C189_b2

namespace C189_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -24, a6 := 45 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 7] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C189_b3

namespace C190_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 2, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C190_a1

namespace C190_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -48, a6 := 147 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C190_b1

namespace C192_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -129, a6 := 609 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
def wildData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 1, 0],              kodaira := -9 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C192_a1

namespace C192_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := 9 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C192_a2

namespace C192_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := -2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C192_a3

namespace C192_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 31, a6 := 33 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
def wildData : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C192_a4

namespace C196_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -142, a6 := 701 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C196_a1

namespace C196_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C196_a2

namespace C197_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -5, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C197_a1

namespace C198_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3168, a6 := 69430 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 11] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C198_a1

namespace C198_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -198, a6 := 1120 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C198_a2

namespace C198_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -108, a6 := 2074 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C198_a3

namespace C198_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 11] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C198_a4

namespace C200_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := 48 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C200_b1

namespace C200_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := -2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C200_b2

namespace C201_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C201_a1

namespace C201_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C201_b1

namespace C201_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -794, a6 := 8289 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C201_c1

namespace C203_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 0, a6 := -2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C203_b1

namespace C205_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -232, a6 := -1286 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a1

namespace C205_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -27, a6 := 26 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a2

namespace C205_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -22, a6 := 44 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a3

namespace C205_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 98, a6 := 126 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C205_a4

namespace C207_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -140, a6 := 668 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 23, 23] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C207_a1

namespace C207_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 20 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 23] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C207_a2

namespace C208_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 32 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13] }
def wildData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C208_b1

namespace C209_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -27, a6 := 55 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C209_a1

namespace C209_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 193, a6 := -308 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C209_a2

namespace C210_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -373, a6 := 2623 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a1

namespace C210_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -23, a6 := 33 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a2

namespace C210_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -3, a6 := -3 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a3

namespace C210_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 7, a6 := 147 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C210_a4

namespace C212_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 8 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 53] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C212_a1

namespace C214_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C214_a1

namespace C214_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -193, a6 := 1012 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C214_b1

namespace C214_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -12, a6 := 16 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C214_c1

namespace C215_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -8, a6 := -12 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C215_a1

namespace C216_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 20 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
def wildData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C216_a1

namespace C218_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C218_a1

namespace C218_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 18, a6 := -104 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C218_a2

namespace C219_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -6, a6 := 8 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_a1

namespace C219_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -27, a6 := -85 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_b1

namespace C219_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 3, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_b2

namespace C219_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1297, a6 := -18530 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_c1

namespace C219_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -82, a6 := -305 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C219_c2

namespace C220_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7100, a6 := -232652 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 11, 11, 11] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C220_a1

namespace C220_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -445, a6 := -3720 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 11, 11, 11, 11, 11, 11] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C220_a2

namespace C220_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -100, a6 := -252 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 11] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C220_a3

namespace C220_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -45, a6 := 100 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 11, 11] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C220_a4

namespace C224_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := -8 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C224_a1

namespace C224_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C224_a2

namespace C225_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -75, a6 := 256 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C225_a1

namespace C225_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 375, a6 := -12344 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 1, 0],                kodaira := -9 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C225_a2

namespace C225_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -34 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C225_c1

namespace C225_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 5, 5] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C225_c2

namespace C226_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -45, a6 := -119 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C226_a1

namespace C226_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -5, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C226_a2

namespace C228_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 9 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 19] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C228_a1

namespace C229_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C229_a1

namespace C232_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 29] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C232_a1

namespace C234_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -63, a6 := 209 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 13, 13] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C234_a1

namespace C234_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 5 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 13] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C234_a2

namespace C235_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -5, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C235_b1

namespace C236_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 59] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C236_a1

namespace C238_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -8, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_a1

namespace C238_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_a2

namespace C238_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -700, a6 := 7056 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_c1

namespace C238_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -60, a6 := 16 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C238_c2

namespace C240_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -216, a6 := 1296 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5] }
def wildData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C240_a1

namespace C240_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -136, a6 := -560 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5] }
def wildData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C240_a2

namespace C240_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 16 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C240_a3

namespace C240_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C240_a4

namespace C242_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -52, a6 := 144 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 3, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C243_a1

namespace C243_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 20 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C243_a2

namespace C244_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 61] }
def wildData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C244_a1

namespace C245_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -7, a6 := 12 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -6435, a6 := 210006 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -65, a6 := -204 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 425, a6 := 433 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -66, a6 := 180 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C246_a1

namespace C246_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -26, a6 := 444 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C246_a2

namespace C248_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C248_a1

namespace C248_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
def wildData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C248_c1

namespace C249_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -55, a6 := 134 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C249_a1

namespace C249_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 2, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C249_b1

namespace C252_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -327, a6 := 2270 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
def wildData : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C252_a1

namespace C252_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 65 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C252_a2

namespace C254_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -5, a6 := -3 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_a1

namespace C254_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -24432, a6 := -1471934 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_b1

namespace C254_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -302, a6 := -2036 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_b2

namespace C254_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -22, a6 := 36 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C254_b3

namespace C256_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C256_a2

namespace C256_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
def wildData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C256_b1

namespace C258_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 3, a6 := -3 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C258_b1

namespace C258_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -15, a6 := 22 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C258_c1

namespace C262_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C262_a1

namespace C262_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 1, a6 := 25 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C262_b1

namespace C265_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -138, a6 := 656 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C265_a1

namespace C265_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -133, a6 := 702 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C265_a2

namespace C269_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -2, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C269_a1

namespace C272_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -48, a6 := -140 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
def wildData : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C272_a1

namespace C272_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17] }
def wildData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C272_a2

namespace C273_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -26, a6 := 68 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C273_a1

namespace C274_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2846, a6 := 59156 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_a1

namespace C274_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_b1

namespace C274_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 8, a6 := -6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_b2

namespace C274_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -7, a6 := 9 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C274_c1

namespace C275_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1480, a6 := 22272 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -730, a6 := -7228 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -105, a6 := 272 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 20, a6 := 22 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
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
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 0, a6 := -1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C277_a1

namespace C278_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1, a6 := 9 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C278_b1

namespace C280_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -412, a6 := 3316 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 7, 7, 7] }
def wildData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C280_a1

namespace C280_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 5 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7] }
def wildData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C280_b1

namespace C282_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -255, a6 := 1461 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C282_a1

namespace C282_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -15, a6 := 21 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C282_a2

namespace C285_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -76, a6 := -19 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_a1

namespace C285_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 19, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_a2

namespace C285_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -93, a6 := -378 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_b1

namespace C285_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 2, a6 := -17 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C285_b2

namespace C37_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C37_a1

namespace C43_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 0, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C43_a1

namespace C5077_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -7, a6 := 6 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C5077_a1

namespace C53_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 0, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C53_a1

namespace C57_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -2, a6 := 2 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C57_a1

namespace C58_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C58_a1

namespace C61_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -2, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C61_a1

namespace C65_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C65_a1

namespace C65_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 4, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C65_a2

namespace C77_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C77_a1

namespace C79_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C79_a1

namespace C82_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -12, a6 := -16 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C82_a1

namespace C82_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C82_a2

namespace C83_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C83_a1

namespace C88_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 4 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
def wildData : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C88_a1

namespace C89_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C89_a1

namespace C91_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 1, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_a1

namespace C91_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -117, a6 := -1245 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_b1

namespace C91_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -7, a6 := 5 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_b2

namespace C91_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 13, a6 := 42 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
theorem semistable : SemistableModel equation := by decide +kernel
theorem sign_negative : semistableSignFast equation = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_semistable_negative equation nonsingular semistable sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_semistable_negative equation nonsingular semistable sign_negative
end C91_b3

namespace C92_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 1 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
def wildData : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C92_a1

namespace C99_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -17, a6 := 30 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 11, 11] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C99_a1

namespace C99_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := 0 }
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel
def witness : MinimalityWitness := { primes := [3, 3, 3, 11] }
def wildData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem wild_valid : wildData.Valid equation := by decide +kernel
theorem sign_negative : wildSignFast equation wildData = -1 := by decide +kernel
theorem central_vanishing : (modularWitness equation nonsingular).formL 1 = 0 :=
  central_zero_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
theorem analytic_rank_at_least_one :
    1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) :=
  rank_lower_bound_of_wild_negative equation nonsingular witness witness_valid wildData wild_valid sign_negative
end C99_a2

def certificateCount : Nat := 229
end VerifiedLcalc.Certificates.NegativeSigns
