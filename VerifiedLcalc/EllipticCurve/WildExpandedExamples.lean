module
public import VerifiedLcalc.EllipticCurve.WildArithmetic
@[expose] public section
namespace VerifiedLcalc.EllipticCurve.WildExpandedExamples
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace C100_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1033, a6 := -12438 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 100 := by decide +kernel
theorem level_formula : wildLevel equation data = 100 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (100 : Nat) = 100 := by decide +kernel
end C100_a1

namespace C100_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -908, a6 := -15688 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 100 := by decide +kernel
theorem level_formula : wildLevel equation data = 100 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (100 : Nat) = 100 := by decide +kernel
end C100_a2

namespace C100_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -33, a6 := 62 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 100 := by decide +kernel
theorem level_formula : wildLevel equation data = 100 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (100 : Nat) = 100 := by decide +kernel
end C100_a3

namespace C100_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 92, a6 := 312 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 100 := by decide +kernel
theorem level_formula : wildLevel equation data = 100 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (100 : Nat) = 100 := by decide +kernel
end C100_a4

namespace C104_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -16, a6 := -32 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 104 := by decide +kernel
theorem level_formula : wildLevel equation data = 104 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (104 : Nat) = 104 := by decide +kernel
end C104_a1

namespace C108_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -108 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 108 := by decide +kernel
theorem level_formula : wildLevel equation data = 108 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (108 : Nat) = 108 := by decide +kernel
end C108_a1

namespace C108_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 108 := by decide +kernel
theorem level_formula : wildLevel equation data = 108 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (108 : Nat) = 108 := by decide +kernel
end C108_a2

namespace C112_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -40, a6 := 84 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_a1

namespace C112_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_a2

namespace C112_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := -1990 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_b1

namespace C112_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := 138 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_b2

namespace C112_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := -30 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_b3

namespace C112_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -2 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_b4

namespace C112_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -43688, a6 := 3529328 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0],              kodaira := -17 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_c1

namespace C112_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2728, a6 := 55920 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],              kodaira := -26 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_c2

namespace C112_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -568, a6 := 4464 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 0],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_c3

namespace C112_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -168, a6 := -784 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_c4

namespace C112_c5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -8, a6 := -16 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_c5

namespace C112_c6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 72, a6 := 368 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 1, 0, 1, 0],              kodaira := -14 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 112 := by decide +kernel
theorem level_formula : wildLevel equation data = 112 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (112 : Nat) = 112 := by decide +kernel
end C112_c6

namespace C116_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4831, a6 := -129242 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 116 := by decide +kernel
theorem level_formula : wildLevel equation data = 116 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (116 : Nat) = 116 := by decide +kernel
end C116_a1

namespace C116_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 116 := by decide +kernel
theorem level_formula : wildLevel equation data = 116 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (116 : Nat) = 116 := by decide +kernel
end C116_b1

namespace C116_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 36, a6 := -76 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 116 := by decide +kernel
theorem level_formula : wildLevel equation data = 116 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (116 : Nat) = 116 := by decide +kernel
end C116_b2

namespace C116_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := 14 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 116 := by decide +kernel
theorem level_formula : wildLevel equation data = 116 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (116 : Nat) = 116 := by decide +kernel
end C116_c1

namespace C116_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 24 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 116 := by decide +kernel
theorem level_formula : wildLevel equation data = 116 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (116 : Nat) = 116 := by decide +kernel
end C116_c2

namespace C117_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -626, a6 := 6180 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 117 := by decide +kernel
theorem level_formula : wildLevel equation data = 117 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (117 : Nat) = 117 := by decide +kernel
end C117_a1

namespace C117_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -176, a6 := -768 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 117 := by decide +kernel
theorem level_formula : wildLevel equation data = 117 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (117 : Nat) = 117 := by decide +kernel
end C117_a2

namespace C117_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -41, a6 := 96 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 117 := by decide +kernel
theorem level_formula : wildLevel equation data = 117 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (117 : Nat) = 117 := by decide +kernel
end C117_a3

namespace C117_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := 6 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 117 := by decide +kernel
theorem level_formula : wildLevel equation data = 117 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (117 : Nat) = 117 := by decide +kernel
end C117_a4

namespace C120_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -216, a6 := -1296 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_a1

namespace C120_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -136, a6 := 560 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_a2

namespace C120_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -16, a6 := -16 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_a3

namespace C120_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 4, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_a4

namespace C120_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3200, a6 := -70752 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_b1

namespace C120_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -200, a6 := -1152 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_b2

namespace C120_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -80, a6 := -2400 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_b3

namespace C120_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -20, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_b4

namespace C120_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -15, a6 := 18 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_b5

namespace C120_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 80, a6 := 80 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 120 := by decide +kernel
theorem level_formula : wildLevel equation data = 120 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (120 : Nat) = 120 := by decide +kernel
end C120_b6

namespace C124_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 124 := by decide +kernel
theorem level_formula : wildLevel equation data = 124 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (124 : Nat) = 124 := by decide +kernel
end C124_a1

namespace C124_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 18, a6 := -11 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 124 := by decide +kernel
theorem level_formula : wildLevel equation data = 124 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (124 : Nat) = 124 := by decide +kernel
end C124_a2

namespace C124_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -17, a6 := -27 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 124 := by decide +kernel
theorem level_formula : wildLevel equation data = 124 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (124 : Nat) = 124 := by decide +kernel
end C124_b1

namespace C126_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -12096, a6 := -509036 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_a1

namespace C126_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -8226, a6 := 286474 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 2, 1],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_a2

namespace C126_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -936, a6 := -3668 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 2, 1, 1, 0, 2, 0],                kodaira := -12 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_a3

namespace C126_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -756, a6 := -7808 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_a4

namespace C126_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -36, a6 := -176 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_a5

namespace C126_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3474, a6 := -31010 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 0, 2, 1, 0, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0],                kodaira := -20 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_a6

namespace C126_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -24575, a6 := 1488935 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_b1

namespace C126_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1535, a6 := 23591 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_b2

namespace C126_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -320, a6 := 1883 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_b3

namespace C126_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -95, a6 := -331 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_b4

namespace C126_b5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := -7 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_b5

namespace C126_b6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 40, a6 := 155 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 126 := by decide +kernel
theorem level_formula : wildLevel equation data = 126 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (126 : Nat) = 126 := by decide +kernel
end C126_b6

namespace C128_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := 7 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_a1

namespace C128_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_a2

namespace C128_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := -2 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_b1

namespace C128_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := -5 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_b2

namespace C128_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := -7 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_c1

namespace C128_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 1, a6 := -1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_c2

namespace C128_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 2 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_d1

namespace C128_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 5 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 128 := by decide +kernel
theorem level_formula : wildLevel equation data = 128 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (128 : Nat) = 128 := by decide +kernel
end C128_d2

namespace C132_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1292, a6 := 18312 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 132 := by decide +kernel
theorem level_formula : wildLevel equation data = 132 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (132 : Nat) = 132 := by decide +kernel
end C132_a1

namespace C132_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -77, a6 := 330 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 132 := by decide +kernel
theorem level_formula : wildLevel equation data = 132 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (132 : Nat) = 132 := by decide +kernel
end C132_a2

namespace C132_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -12, a6 := -12 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 132 := by decide +kernel
theorem level_formula : wildLevel equation data = 132 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (132 : Nat) = 132 := by decide +kernel
end C132_b1

namespace C132_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 132 := by decide +kernel
theorem level_formula : wildLevel equation data = 132 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (132 : Nat) = 132 := by decide +kernel
end C132_b2

namespace C135_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 4 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 135 := by decide +kernel
theorem level_formula : wildLevel equation data = 135 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (135 : Nat) = 135 := by decide +kernel
end C135_a1

namespace C135_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := -115 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 135 := by decide +kernel
theorem level_formula : wildLevel equation data = 135 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (135 : Nat) = 135 := by decide +kernel
end C135_b1

namespace C136_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 136 := by decide +kernel
theorem level_formula : wildLevel equation data = 136 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (136 : Nat) = 136 := by decide +kernel
end C136_a1

namespace C136_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 16 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 136 := by decide +kernel
theorem level_formula : wildLevel equation data = 136 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (136 : Nat) = 136 := by decide +kernel
end C136_a2

namespace C136_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -48, a6 := 140 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 136 := by decide +kernel
theorem level_formula : wildLevel equation data = 136 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (136 : Nat) = 136 := by decide +kernel
end C136_b1

namespace C136_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -8, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 136 := by decide +kernel
theorem level_formula : wildLevel equation data = 136 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (136 : Nat) = 136 := by decide +kernel
end C136_b2

namespace C140_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -805, a6 := -9065 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 140 := by decide +kernel
theorem level_formula : wildLevel equation data = 140 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (140 : Nat) = 140 := by decide +kernel
end C140_a1

namespace C140_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -25 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 140 := by decide +kernel
theorem level_formula : wildLevel equation data = 140 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (140 : Nat) = 140 := by decide +kernel
end C140_a2

namespace C140_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 32, a6 := 212 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 140 := by decide +kernel
theorem level_formula : wildLevel equation data = 140 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (140 : Nat) = 140 := by decide +kernel
end C140_b1

namespace C144_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -135, a6 := 594 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_a1

namespace C144_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -15, a6 := -22 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_a2

namespace C144_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -1 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_a3

namespace C144_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 27 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_a4

namespace C144_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3459, a6 := -78302 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_b1

namespace C144_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -579, a6 := 5362 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_b2

namespace C144_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -219, a6 := -1190 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 0],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_b3

namespace C144_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := 70 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_b4

namespace C144_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 6, a6 := 7 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_b5

namespace C144_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 141, a6 := -4718 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 0, 0, 0, 0, 0],                kodaira := -12 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 144 := by decide +kernel
theorem level_formula : wildLevel equation data = 144 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (144 : Nat) = 144 := by decide +kernel
end C144_b6

namespace C148_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 148 := by decide +kernel
theorem level_formula : wildLevel equation data = 148 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (148 : Nat) = 148 := by decide +kernel
end C148_a1

namespace C152_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 3 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 152 := by decide +kernel
theorem level_formula : wildLevel equation data = 152 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (152 : Nat) = 152 := by decide +kernel
end C152_a1

namespace C152_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := -16 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 152 := by decide +kernel
theorem level_formula : wildLevel equation data = 152 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (152 : Nat) = 152 := by decide +kernel
end C152_b1

namespace C153_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 2 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_a1

namespace C153_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -534, a6 := 4752 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_b1

namespace C153_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 27 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 0],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_b2

namespace C153_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -816, a6 := 9179 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_c1

namespace C153_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -51, a6 := 152 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_c2

namespace C153_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := -1 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_c3

namespace C153_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := 377 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_c4

namespace C153_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := -61 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 153 := by decide +kernel
theorem level_formula : wildLevel equation data = 153 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (153 : Nat) = 153 := by decide +kernel
end C153_d1

namespace C156_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := -24 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 156 := by decide +kernel
theorem level_formula : wildLevel equation data = 156 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (156 : Nat) = 156 := by decide +kernel
end C156_a1

namespace C156_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 6 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 156 := by decide +kernel
theorem level_formula : wildLevel equation data = 156 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (156 : Nat) = 156 := by decide +kernel
end C156_a2

namespace C156_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -748, a6 := -7564 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 156 := by decide +kernel
theorem level_formula : wildLevel equation data = 156 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (156 : Nat) = 156 := by decide +kernel
end C156_b1

namespace C156_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -733, a6 := -7888 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 156 := by decide +kernel
theorem level_formula : wildLevel equation data = 156 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (156 : Nat) = 156 := by decide +kernel
end C156_b2

namespace C156_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -148, a6 := 644 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 156 := by decide +kernel
theorem level_formula : wildLevel equation data = 156 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (156 : Nat) = 156 := by decide +kernel
end C156_b3

namespace C156_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := -4 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 156 := by decide +kernel
theorem level_formula : wildLevel equation data = 156 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (156 : Nat) = 156 := by decide +kernel
end C156_b4

namespace C160_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -6, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 160 := by decide +kernel
theorem level_formula : wildLevel equation data = 160 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (160 : Nat) = 160 := by decide +kernel
end C160_a1

namespace C160_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 15 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 160 := by decide +kernel
theorem level_formula : wildLevel equation data = 160 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (160 : Nat) = 160 := by decide +kernel
end C160_a2

namespace C160_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -6, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 160 := by decide +kernel
theorem level_formula : wildLevel equation data = 160 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (160 : Nat) = 160 := by decide +kernel
end C160_b1

namespace C160_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := -15 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 160 := by decide +kernel
theorem level_formula : wildLevel equation data = 160 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (160 : Nat) = 160 := by decide +kernel
end C160_b2

namespace C162_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := 8 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_a1

namespace C162_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 39, a6 := -19 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_a2

namespace C162_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1077, a6 := 13877 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_b1

namespace C162_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -852, a6 := 19664 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_b2

namespace C162_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -42, a6 := -100 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_b3

namespace C162_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3, a6 := -1 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_b4

namespace C162_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -9695, a6 := -364985 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_c1

namespace C162_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -95, a6 := -697 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_c2

namespace C162_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 5 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_c3

namespace C162_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 25, a6 := 1 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_c4

namespace C162_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -56, a6 := -161 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_d1

namespace C162_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := -1 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 162 := by decide +kernel
theorem level_formula : wildLevel equation data = 162 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (162 : Nat) = 162 := by decide +kernel
end C162_d2

namespace C168_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4032, a6 := 99900 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_a1

namespace C168_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -392, a6 := -228 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_a2

namespace C168_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -252, a6 := 1620 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_a3

namespace C168_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -7, a6 := 52 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_a4

namespace C168_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -152, a6 := 672 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_b1

namespace C168_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -12, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_b2

namespace C168_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7, a6 := -10 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_b3

namespace C168_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 48, a6 := 48 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 168 := by decide +kernel
theorem level_formula : wildLevel equation data = 168 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (168 : Nat) = 168 := by decide +kernel
end C168_b4

namespace C171_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -914, a6 := -10402 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 0, 2],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_a1

namespace C171_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -59, a6 := -142 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_a2

namespace C171_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := 20 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_a3

namespace C171_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 76, a6 := -790 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_a4

namespace C171_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -6924, a6 := 221760 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_b1

namespace C171_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -84, a6 := 315 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_b2

namespace C171_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 0 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_b3

namespace C171_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -39513, a6 := 3023145 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_c1

namespace C171_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 177, a6 := 1035 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 1, 1, 1, 2, 1, 0, 1],                kodaira := -14 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_c2

namespace C171_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -21, a6 := -41 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 171 := by decide +kernel
theorem level_formula : wildLevel equation data = 171 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (171 : Nat) = 171 := by decide +kernel
end C171_d1

namespace C172_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := 15 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 172 := by decide +kernel
theorem level_formula : wildLevel equation data = 172 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (172 : Nat) = 172 := by decide +kernel
end C172_a1

namespace C172_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 67, a6 := 79 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 172 := by decide +kernel
theorem level_formula : wildLevel equation data = 172 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (172 : Nat) = 172 := by decide +kernel
end C172_a2

namespace C176_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -77, a6 := 289 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 176 := by decide +kernel
theorem level_formula : wildLevel equation data = 176 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (176 : Nat) = 176 := by decide +kernel
end C176_a1

namespace C176_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 176 := by decide +kernel
theorem level_formula : wildLevel equation data = 176 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (176 : Nat) = 176 := by decide +kernel
end C176_a2

namespace C176_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -125125, a6 := 16994227 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 176 := by decide +kernel
theorem level_formula : wildLevel equation data = 176 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (176 : Nat) = 176 := by decide +kernel
end C176_b1

namespace C176_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -165, a6 := 1427 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 176 := by decide +kernel
theorem level_formula : wildLevel equation data = 176 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (176 : Nat) = 176 := by decide +kernel
end C176_b2

namespace C176_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -13 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 176 := by decide +kernel
theorem level_formula : wildLevel equation data = 176 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (176 : Nat) = 176 := by decide +kernel
end C176_b3

namespace C176_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 176 := by decide +kernel
theorem level_formula : wildLevel equation data = 176 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (176 : Nat) = 176 := by decide +kernel
end C176_c1

namespace C180_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -372, a6 := 2761 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 180 := by decide +kernel
theorem level_formula : wildLevel equation data = 180 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (180 : Nat) = 180 := by decide +kernel
end C180_a1

namespace C180_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -327, a6 := 3454 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 180 := by decide +kernel
theorem level_formula : wildLevel equation data = 180 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (180 : Nat) = 180 := by decide +kernel
end C180_a2

namespace C180_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := -11 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 180 := by decide +kernel
theorem level_formula : wildLevel equation data = 180 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (180 : Nat) = 180 := by decide +kernel
end C180_a3

namespace C180_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 33, a6 := -74 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 180 := by decide +kernel
theorem level_formula : wildLevel equation data = 180 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (180 : Nat) = 180 := by decide +kernel
end C180_a4

namespace C184_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 184 := by decide +kernel
theorem level_formula : wildLevel equation data = 184 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (184 : Nat) = 184 := by decide +kernel
end C184_a1

namespace C184_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 5 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 184 := by decide +kernel
theorem level_formula : wildLevel equation data = 184 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (184 : Nat) = 184 := by decide +kernel
end C184_b1

namespace C184_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -35, a6 := 62 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 184 := by decide +kernel
theorem level_formula : wildLevel equation data = 184 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (184 : Nat) = 184 := by decide +kernel
end C184_c1

namespace C184_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 5, a6 := 6 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 184 := by decide +kernel
theorem level_formula : wildLevel equation data = 184 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (184 : Nat) = 184 := by decide +kernel
end C184_c2

namespace C184_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -55, a6 := -157 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 184 := by decide +kernel
theorem level_formula : wildLevel equation data = 184 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (184 : Nat) = 184 := by decide +kernel
end C184_d1

namespace C189_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 0 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_a1

namespace C189_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3834, a6 := -91375 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_b1

namespace C189_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -54, a6 := -88 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_b2

namespace C189_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -24, a6 := 45 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_b3

namespace C189_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -426, a6 := 3384 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_c1

namespace C189_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -216, a6 := -1222 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_c2

namespace C189_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -6, a6 := 3 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_c3

namespace C189_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := -7 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 189 := by decide +kernel
theorem level_formula : wildLevel equation data = 189 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (189 : Nat) = 189 := by decide +kernel
end C189_d1

namespace C192_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -129, a6 := 609 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_a1

namespace C192_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := 9 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_a2

namespace C192_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := -2 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_a3

namespace C192_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 31, a6 := 33 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_a4

namespace C192_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1537, a6 := 23713 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 0, 0, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_b1

namespace C192_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -257, a6 := -1503 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 0, 1, 1],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_b2

namespace C192_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -97, a6 := 385 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 0, 0, 0],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_b3

namespace C192_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -17, a6 := -15 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_b4

namespace C192_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := -3 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_b5

namespace C192_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 63, a6 := 1377 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1, 0, 0, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_b6

namespace C192_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -129, a6 := -609 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_c1

namespace C192_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := -9 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_c2

namespace C192_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 2 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_c3

namespace C192_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 31, a6 := -33 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 1, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_c4

namespace C192_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1537, a6 := -23713 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0, 1, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_d1

namespace C192_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -257, a6 := 1503 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0, 0, 1],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_d2

namespace C192_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -97, a6 := -385 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0, 1, 0],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_d3

namespace C192_d4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -17, a6 := 15 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_d4

namespace C192_d5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := 3 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_d5

namespace C192_d6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 63, a6 := -1377 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 0, 1, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 192 := by decide +kernel
theorem level_formula : wildLevel equation data = 192 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (192 : Nat) = 192 := by decide +kernel
end C192_d6

namespace C196_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -142, a6 := 701 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 196 := by decide +kernel
theorem level_formula : wildLevel equation data = 196 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (196 : Nat) = 196 := by decide +kernel
end C196_a1

namespace C196_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 196 := by decide +kernel
theorem level_formula : wildLevel equation data = 196 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (196 : Nat) = 196 := by decide +kernel
end C196_a2

namespace C196_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -6974, a6 := -226507 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 196 := by decide +kernel
theorem level_formula : wildLevel equation data = 196 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (196 : Nat) = 196 := by decide +kernel
end C196_b1

namespace C196_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -114, a6 := -127 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 196 := by decide +kernel
theorem level_formula : wildLevel equation data = 196 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (196 : Nat) = 196 := by decide +kernel
end C196_b2

namespace C198_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3168, a6 := 69430 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_a1

namespace C198_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -198, a6 := 1120 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_a2

namespace C198_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -108, a6 := 2074 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 0, 1],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_a3

namespace C198_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := 4 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_a4

namespace C198_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -9222, a6 := -338572 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_b1

namespace C198_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -582, a6 := -5068 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_b2

namespace C198_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -147, a6 := -135 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_b3

namespace C198_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -87, a6 := 333 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_b4

namespace C198_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90585, a6 := 10516473 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_c1

namespace C198_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90495, a6 := 10538343 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_c2

namespace C198_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -405, a6 := -2187 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0, 0, 2],                kodaira := -9 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_c3

namespace C198_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1035, a6 := -15147 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2, 0, 2, 1, 0, 2, 0, 0, 1],                kodaira := -14 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_c4

namespace C198_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1325, a6 := 4969 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_d1

namespace C198_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1025, a6 := 12881 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_d2

namespace C198_d3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -785, a6 := -8207 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_d3

namespace C198_d4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -65, a6 := 209 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_d4

namespace C198_e1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -725, a6 := 7661 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_e1

namespace C198_e2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -365, a6 := 15005 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_e2

namespace C198_e3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -50, a6 := -115 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 1],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_e3

namespace C198_e4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 40, a6 := -547 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 0, 1, 1, 2],                kodaira := -10 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 198 := by decide +kernel
theorem level_formula : wildLevel equation data = 198 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (198 : Nat) = 198 := by decide +kernel
end C198_e4

namespace C20_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -41, a6 := -116 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 20 := by decide +kernel
theorem level_formula : wildLevel equation data = 20 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (20 : Nat) = 20 := by decide +kernel
end C20_a1

namespace C20_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -36, a6 := -140 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 20 := by decide +kernel
theorem level_formula : wildLevel equation data = 20 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (20 : Nat) = 20 := by decide +kernel
end C20_a2

namespace C20_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 20 := by decide +kernel
theorem level_formula : wildLevel equation data = 20 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (20 : Nat) = 20 := by decide +kernel
end C20_a3

namespace C20_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 4, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 20 := by decide +kernel
theorem level_formula : wildLevel equation data = 20 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (20 : Nat) = 20 := by decide +kernel
end C20_a4

namespace C200_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 125, a6 := -1250 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_a1

namespace C200_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := 48 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_b1

namespace C200_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := -2 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_b2

namespace C200_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2675, a6 := -53250 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_c1

namespace C200_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -175, a6 := -750 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_c2

namespace C200_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -50, a6 := 125 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_c3

namespace C200_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 325, a6 := -4250 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_c4

namespace C200_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -708, a6 := 7412 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_d1

namespace C200_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -83, a6 := -88 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_d2

namespace C200_e1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 5, a6 := -10 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 200 := by decide +kernel
theorem level_formula : wildLevel equation data = 200 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (200 : Nat) = 200 := by decide +kernel
end C200_e1

namespace C204_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1621, a6 := -24623 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 204 := by decide +kernel
theorem level_formula : wildLevel equation data = 204 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (204 : Nat) = 204 := by decide +kernel
end C204_a1

namespace C204_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -9 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 204 := by decide +kernel
theorem level_formula : wildLevel equation data = 204 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (204 : Nat) = 204 := by decide +kernel
end C204_b1

namespace C207_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -140, a6 := 668 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 207 := by decide +kernel
theorem level_formula : wildLevel equation data = 207 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (207 : Nat) = 207 := by decide +kernel
end C207_a1

namespace C207_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 20 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 207 := by decide +kernel
theorem level_formula : wildLevel equation data = 207 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (207 : Nat) = 207 := by decide +kernel
end C207_a2

namespace C208_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -7352, a6 := 245104 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0],              kodaira := -17 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_a1

namespace C208_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -72, a6 := 496 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 0, 0],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_a2

namespace C208_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -16 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_a3

namespace C208_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 32 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_b1

namespace C208_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 3 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_c1

namespace C208_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 10 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_c2

namespace C208_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3403, a6 := 83834 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_d1

namespace C208_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -43, a6 := -166 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 0, 1, 1, 0, 1, 1],              kodaira := -15 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 208 := by decide +kernel
theorem level_formula : wildLevel equation data = 208 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (208 : Nat) = 208 := by decide +kernel
end C208_d2

namespace C212_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 8 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 212 := by decide +kernel
theorem level_formula : wildLevel equation data = 212 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (212 : Nat) = 212 := by decide +kernel
end C212_a1

namespace C212_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -17, a6 := -22 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 212 := by decide +kernel
theorem level_formula : wildLevel equation data = 212 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (212 : Nat) = 212 := by decide +kernel
end C212_b1

namespace C212_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := -40 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 212 := by decide +kernel
theorem level_formula : wildLevel equation data = 212 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (212 : Nat) = 212 := by decide +kernel
end C212_b2

namespace C216_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 20 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 216 := by decide +kernel
theorem level_formula : wildLevel equation data = 216 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (216 : Nat) = 216 := by decide +kernel
end C216_a1

namespace C216_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := -34 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 216 := by decide +kernel
theorem level_formula : wildLevel equation data = 216 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (216 : Nat) = 216 := by decide +kernel
end C216_b1

namespace C216_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -27, a6 := 918 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 216 := by decide +kernel
theorem level_formula : wildLevel equation data = 216 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (216 : Nat) = 216 := by decide +kernel
end C216_c1

namespace C216_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -108, a6 := -540 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 216 := by decide +kernel
theorem level_formula : wildLevel equation data = 216 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (216 : Nat) = 216 := by decide +kernel
end C216_d1

namespace C220_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7100, a6 := -232652 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 220 := by decide +kernel
theorem level_formula : wildLevel equation data = 220 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (220 : Nat) = 220 := by decide +kernel
end C220_a1

namespace C220_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -445, a6 := -3720 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 220 := by decide +kernel
theorem level_formula : wildLevel equation data = 220 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (220 : Nat) = 220 := by decide +kernel
end C220_a2

namespace C220_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -100, a6 := -252 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 220 := by decide +kernel
theorem level_formula : wildLevel equation data = 220 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (220 : Nat) = 220 := by decide +kernel
end C220_a3

namespace C220_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -45, a6 := 100 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 220 := by decide +kernel
theorem level_formula : wildLevel equation data = 220 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (220 : Nat) = 220 := by decide +kernel
end C220_a4

namespace C220_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -60, a6 := 200 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 220 := by decide +kernel
theorem level_formula : wildLevel equation data = 220 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (220 : Nat) = 220 := by decide +kernel
end C220_b1

namespace C220_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 2 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 220 := by decide +kernel
theorem level_formula : wildLevel equation data = 220 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (220 : Nat) = 220 := by decide +kernel
end C220_b2

namespace C224_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := -8 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 224 := by decide +kernel
theorem level_formula : wildLevel equation data = 224 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (224 : Nat) = 224 := by decide +kernel
end C224_a1

namespace C224_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 224 := by decide +kernel
theorem level_formula : wildLevel equation data = 224 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (224 : Nat) = 224 := by decide +kernel
end C224_a2

namespace C224_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -8, a6 := 8 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 224 := by decide +kernel
theorem level_formula : wildLevel equation data = 224 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (224 : Nat) = 224 := by decide +kernel
end C224_b1

namespace C224_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 2, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 224 := by decide +kernel
theorem level_formula : wildLevel equation data = 224 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (224 : Nat) = 224 := by decide +kernel
end C224_b2

namespace C225_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -75, a6 := 256 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_a1

namespace C225_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 375, a6 := -12344 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 1, 0],                kodaira := -9 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_a2

namespace C225_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -486005, a6 := 130530872 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b1

namespace C225_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -30380, a6 := 2044622 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2, 1, 0, 0, 1],                kodaira := -12 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b2

namespace C225_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -24755, a6 := 2820872 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 1, 0, 2, 0, 2, 0, 2, 0, 1, 2, 0, 2, 2, 1],                kodaira := -20 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b3

namespace C225_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -18005, a6 := -925378 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b4

namespace C225_b5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2255, a6 := 19622 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 1, 2],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b5

namespace C225_b6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1130, a6 := -14128 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b6

namespace C225_b7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := -628 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b7

namespace C225_b8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 7870, a6 := 141122 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_b8

namespace C225_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -34 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_c1

namespace C225_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 1 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_c2

namespace C225_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -4219 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_d1

namespace C225_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 156 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_d2

namespace C225_e1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1875, a6 := 32031 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_e1

namespace C225_e2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 15, a6 := -99 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 1, 0],                kodaira := -9 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 225 := by decide +kernel
theorem level_formula : wildLevel equation data = 225 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (225 : Nat) = 225 := by decide +kernel
end C225_e2

namespace C228_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 9 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 228 := by decide +kernel
theorem level_formula : wildLevel equation data = 228 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (228 : Nat) = 228 := by decide +kernel
end C228_a1

namespace C228_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -92, a6 := 360 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 228 := by decide +kernel
theorem level_formula : wildLevel equation data = 228 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (228 : Nat) = 228 := by decide +kernel
end C228_b1

namespace C228_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 18 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 228 := by decide +kernel
theorem level_formula : wildLevel equation data = 228 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (228 : Nat) = 228 := by decide +kernel
end C228_b2

namespace C232_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 232 := by decide +kernel
theorem level_formula : wildLevel equation data = 232 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (232 : Nat) = 232 := by decide +kernel
end C232_a1

namespace C232_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -80, a6 := -304 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 232 := by decide +kernel
theorem level_formula : wildLevel equation data = 232 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (232 : Nat) = 232 := by decide +kernel
end C232_b1

namespace C234_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -63, a6 := 209 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_a1

namespace C234_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 5 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_a2

namespace C234_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1914, a6 := 35846 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_b1

namespace C234_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := -64 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_b2

namespace C234_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -186656, a6 := -30992493 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2, 1],                kodaira := -9 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_c1

namespace C234_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -21056, a6 := 404115 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 2, 0, 2, 0, 0, 1, 1, 2, 2, 1, 0, 2, 2, 1, 0, 2, 2, 1],                kodaira := -24 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_c2

namespace C234_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11696, a6 := -479469 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2, 1, 0, 1, 2, 0, 2],                kodaira := -14 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_c3

namespace C234_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -176, a6 := -18669 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2, 1, 2],                kodaira := -9 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_c4

namespace C234_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -569, a6 := -5075 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_d1

namespace C234_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := -107 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_d2

namespace C234_e1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -4136, a6 := 103403 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_e1

namespace C234_e2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -41, a6 := 209 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_e2

namespace C234_e3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := -7 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 234 := by decide +kernel
theorem level_formula : wildLevel equation data = 234 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (234 : Nat) = 234 := by decide +kernel
end C234_e3

namespace C236_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 2 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 236 := by decide +kernel
theorem level_formula : wildLevel equation data = 236 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (236 : Nat) = 236 := by decide +kernel
end C236_a1

namespace C236_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := 8 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 236 := by decide +kernel
theorem level_formula : wildLevel equation data = 236 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (236 : Nat) = 236 := by decide +kernel
end C236_b1

namespace C236_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 31, a6 := 68 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 236 := by decide +kernel
theorem level_formula : wildLevel equation data = 236 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (236 : Nat) = 236 := by decide +kernel
end C236_b2

namespace C24_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -384, a6 := -2772 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 24 := by decide +kernel
theorem level_formula : wildLevel equation data = 24 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (24 : Nat) = 24 := by decide +kernel
end C24_a1

namespace C24_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -64, a6 := 220 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 24 := by decide +kernel
theorem level_formula : wildLevel equation data = 24 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (24 : Nat) = 24 := by decide +kernel
end C24_a2

namespace C24_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -24, a6 := -36 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 24 := by decide +kernel
theorem level_formula : wildLevel equation data = 24 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (24 : Nat) = 24 := by decide +kernel
end C24_a3

namespace C24_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 24 := by decide +kernel
theorem level_formula : wildLevel equation data = 24 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (24 : Nat) = 24 := by decide +kernel
end C24_a4

namespace C24_a5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 1, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 24 := by decide +kernel
theorem level_formula : wildLevel equation data = 24 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (24 : Nat) = 24 := by decide +kernel
end C24_a5

namespace C24_a6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 16, a6 := -180 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 24 := by decide +kernel
theorem level_formula : wildLevel equation data = 24 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (24 : Nat) = 24 := by decide +kernel
end C24_a6

namespace C240_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -216, a6 := 1296 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_a1

namespace C240_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -136, a6 := -560 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_a2

namespace C240_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 16 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_a3

namespace C240_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_a4

namespace C240_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -85336, a6 := 9623536 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b1

namespace C240_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -7256, a6 := 34800 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b2

namespace C240_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5336, a6 := 151536 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 1, 0, 0, 1, 1],              kodaira := -14 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b3

namespace C240_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4616, a6 := -119184 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b4

namespace C240_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1096, a6 := 12400 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 1],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b5

namespace C240_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -296, a6 := -1680 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 0],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b6

namespace C240_b7
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -216, a6 := 4080 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0],              kodaira := -20 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b7

namespace C240_b8
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 24, a6 := -144 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1, 0, 1, 0, 1],              kodaira := -12 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_b8

namespace C240_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -3200, a6 := 70752 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_c1

namespace C240_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -200, a6 := 1152 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_c2

namespace C240_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -80, a6 := 2400 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_c3

namespace C240_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_c4

namespace C240_c5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -15, a6 := -18 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_c5

namespace C240_c6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 80, a6 := -80 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_c6

namespace C240_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -34560, a6 := 2461428 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 1],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d1

namespace C240_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2160, a6 := 37908 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d2

namespace C240_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1760, a6 := 52788 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 1],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d3

namespace C240_d4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1280, a6 := -18060 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 1],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d4

namespace C240_d5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -160, a6 := 308 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 1],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d5

namespace C240_d6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -80, a6 := -300 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d6

namespace C240_d7
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := -12 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 1],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d7

namespace C240_d8
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 560, a6 := 2900 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 240 := by decide +kernel
theorem level_formula : wildLevel equation data = 240 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (240 : Nat) = 240 := by decide +kernel
end C240_d8

namespace C243_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -1 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 243 := by decide +kernel
theorem level_formula : wildLevel equation data = 243 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (243 : Nat) = 243 := by decide +kernel
end C243_a1

namespace C243_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 20 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 243 := by decide +kernel
theorem level_formula : wildLevel equation data = 243 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (243 : Nat) = 243 := by decide +kernel
end C243_a2

namespace C243_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -61 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 243 := by decide +kernel
theorem level_formula : wildLevel equation data = 243 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (243 : Nat) = 243 := by decide +kernel
end C243_b1

namespace C243_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 2 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 243 := by decide +kernel
theorem level_formula : wildLevel equation data = 243 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (243 : Nat) = 243 := by decide +kernel
end C243_b2

namespace C244_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 6 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 244 := by decide +kernel
theorem level_formula : wildLevel equation data = 244 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (244 : Nat) = 244 := by decide +kernel
end C244_a1

namespace C248_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 248 := by decide +kernel
theorem level_formula : wildLevel equation data = 248 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (248 : Nat) = 248 := by decide +kernel
end C248_a1

namespace C248_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -32, a6 := -32 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 248 := by decide +kernel
theorem level_formula : wildLevel equation data = 248 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (248 : Nat) = 248 := by decide +kernel
end C248_b1

namespace C248_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 8, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 248 := by decide +kernel
theorem level_formula : wildLevel equation data = 248 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (248 : Nat) = 248 := by decide +kernel
end C248_b2

namespace C248_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -1 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 248 := by decide +kernel
theorem level_formula : wildLevel equation data = 248 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (248 : Nat) = 248 := by decide +kernel
end C248_c1

namespace C252_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -327, a6 := 2270 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 252 := by decide +kernel
theorem level_formula : wildLevel equation data = 252 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (252 : Nat) = 252 := by decide +kernel
end C252_a1

namespace C252_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 65 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 252 := by decide +kernel
theorem level_formula : wildLevel equation data = 252 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (252 : Nat) = 252 := by decide +kernel
end C252_a2

namespace C252_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -16455, a6 := 812446 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 252 := by decide +kernel
theorem level_formula : wildLevel equation data = 252 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (252 : Nat) = 252 := by decide +kernel
end C252_b1

namespace C252_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1020, a6 := 12913 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 252 := by decide +kernel
theorem level_formula : wildLevel equation data = 252 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (252 : Nat) = 252 := by decide +kernel
end C252_b2

namespace C252_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -255, a6 := 502 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 0, 0, 0, 0],                kodaira := -10 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 252 := by decide +kernel
theorem level_formula : wildLevel equation data = 252 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (252 : Nat) = 252 := by decide +kernel
end C252_b3

namespace C252_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 60, a6 := 61 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 252 := by decide +kernel
theorem level_formula : wildLevel equation data = 252 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (252 : Nat) = 252 := by decide +kernel
end C252_b4

namespace C256_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := -21 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_a1

namespace C256_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := 1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_a2

namespace C256_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_b1

namespace C256_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 8, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_b2

namespace C256_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -8, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_c1

namespace C256_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 2, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_c2

namespace C256_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := 21 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_d1

namespace C256_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -3, a6 := -1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 256 := by decide +kernel
theorem level_formula : wildLevel equation data = 256 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (256 : Nat) = 256 := by decide +kernel
end C256_d2

namespace C260_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -281, a6 := 1910 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 260 := by decide +kernel
theorem level_formula : wildLevel equation data = 260 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (260 : Nat) = 260 := by decide +kernel
end C260_a1

namespace C260_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -276, a6 := 1976 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 260 := by decide +kernel
theorem level_formula : wildLevel equation data = 260 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (260 : Nat) = 260 := by decide +kernel
end C260_a2

namespace C264_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -472, a6 := 4108 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_a1

namespace C264_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -32, a6 := 60 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_a2

namespace C264_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := -12 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_a3

namespace C264_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 88, a6 := 300 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_a4

namespace C264_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -704, a6 := 6960 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_b1

namespace C264_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -104, a6 := -288 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_b2

namespace C264_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -44, a6 := 96 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_b3

namespace C264_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 6 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_b4

namespace C264_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_c1

namespace C264_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 32, a6 := 32 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_c2

namespace C264_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8016, a6 := -278928 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_d1

namespace C264_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7976, a6 := -281808 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 264 := by decide +kernel
theorem level_formula : wildLevel equation data = 264 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (264 : Nat) = 264 := by decide +kernel
end C264_d2

namespace C268_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := -7 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 268 := by decide +kernel
theorem level_formula : wildLevel equation data = 268 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (268 : Nat) = 268 := by decide +kernel
end C268_a1

namespace C27_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -270, a6 := -1708 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 27 := by decide +kernel
theorem level_formula : wildLevel equation data = 27 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (27 : Nat) = 27 := by decide +kernel
end C27_a1

namespace C27_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -30, a6 := 63 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 27 := by decide +kernel
theorem level_formula : wildLevel equation data = 27 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (27 : Nat) = 27 := by decide +kernel
end C27_a2

namespace C27_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -7 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 27 := by decide +kernel
theorem level_formula : wildLevel equation data = 27 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (27 : Nat) = 27 := by decide +kernel
end C27_a3

namespace C27_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 0 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 27 := by decide +kernel
theorem level_formula : wildLevel equation data = 27 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (27 : Nat) = 27 := by decide +kernel
end C27_a4

namespace C270_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15, a6 := 35 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_a1

namespace C270_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 120, a6 := -424 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_a2

namespace C270_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -159, a6 := 813 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_b1

namespace C270_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 66, a6 := 2708 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_b2

namespace C270_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1433, a6 := -20519 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_c1

namespace C270_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 7, a6 := -103 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_c2

namespace C270_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := -1 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_d1

namespace C270_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 13, a6 := 11 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 270 := by decide +kernel
theorem level_formula : wildLevel equation data = 270 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (270 : Nat) = 270 := by decide +kernel
end C270_d2

namespace C272_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -48, a6 := -140 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_a1

namespace C272_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_a2

namespace C272_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1451, a6 := 21274 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_b1

namespace C272_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -91, a6 := 330 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 1],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_b2

namespace C272_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -6 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_b3

namespace C272_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := 890 }
def data : WildData := { atTwo := some { r := 1,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 1, 0],              kodaira := -8 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_b4

namespace C272_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_c1

namespace C272_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 16, a6 := -16 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_c2

namespace C272_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1808, a6 := 21056 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_d1

namespace C272_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1648, a6 := 26304 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 1, 0],              kodaira := -10 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_d2

namespace C272_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -688, a6 := -6720 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 1, 1, 1],              kodaira := -11 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_d3

namespace C272_d4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -48, a6 := -64 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [0, 0, 1, 1, 1, 0, 1, 0, 1],              kodaira := -14 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 272 := by decide +kernel
theorem level_formula : wildLevel equation data = 272 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (272 : Nat) = 272 := by decide +kernel
end C272_d4

namespace C280_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -412, a6 := 3316 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 280 := by decide +kernel
theorem level_formula : wildLevel equation data = 280 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (280 : Nat) = 280 := by decide +kernel
end C280_a1

namespace C280_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 5 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 280 := by decide +kernel
theorem level_formula : wildLevel equation data = 280 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (280 : Nat) = 280 := by decide +kernel
end C280_b1

namespace C32_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -14 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 32 := by decide +kernel
theorem level_formula : wildLevel equation data = 32 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (32 : Nat) = 32 := by decide +kernel
end C32_a1

namespace C32_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := 14 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 32 := by decide +kernel
theorem level_formula : wildLevel equation data = 32 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (32 : Nat) = 32 := by decide +kernel
end C32_a2

namespace C32_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 32 := by decide +kernel
theorem level_formula : wildLevel equation data = 32 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (32 : Nat) = 32 := by decide +kernel
end C32_a3

namespace C32_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 4, a6 := 0 }
def data : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 32 := by decide +kernel
theorem level_formula : wildLevel equation data = 32 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (32 : Nat) = 32 := by decide +kernel
end C32_a4

namespace C36_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -135, a6 := -594 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 36 := by decide +kernel
theorem level_formula : wildLevel equation data = 36 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (36 : Nat) = 36 := by decide +kernel
end C36_a1

namespace C36_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -15, a6 := 22 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 36 := by decide +kernel
theorem level_formula : wildLevel equation data = 36 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (36 : Nat) = 36 := by decide +kernel
end C36_a2

namespace C36_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -27 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 36 := by decide +kernel
theorem level_formula : wildLevel equation data = 36 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (36 : Nat) = 36 := by decide +kernel
end C36_a3

namespace C36_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 36 := by decide +kernel
theorem level_formula : wildLevel equation data = 36 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (36 : Nat) = 36 := by decide +kernel
end C36_a4

namespace C40_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -107, a6 := -426 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 40 := by decide +kernel
theorem level_formula : wildLevel equation data = 40 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (40 : Nat) = 40 := by decide +kernel
end C40_a1

namespace C40_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := -6 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 40 := by decide +kernel
theorem level_formula : wildLevel equation data = 40 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (40 : Nat) = 40 := by decide +kernel
end C40_a2

namespace C40_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 40 := by decide +kernel
theorem level_formula : wildLevel equation data = 40 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (40 : Nat) = 40 := by decide +kernel
end C40_a3

namespace C40_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 13, a6 := -34 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 40 := by decide +kernel
theorem level_formula : wildLevel equation data = 40 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (40 : Nat) = 40 := by decide +kernel
end C40_a4

namespace C44_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -77, a6 := -289 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 44 := by decide +kernel
theorem level_formula : wildLevel equation data = 44 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (44 : Nat) = 44 := by decide +kernel
end C44_a1

namespace C44_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := -1 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 44 := by decide +kernel
theorem level_formula : wildLevel equation data = 44 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (44 : Nat) = 44 := by decide +kernel
end C44_a2

namespace C45_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -19440, a6 := 1048135 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 2],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a1

namespace C45_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1215, a6 := 16600 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 2, 1, 0, 2, 0],                kodaira := -12 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a2

namespace C45_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -990, a6 := 22765 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 0, 2, 2, 1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0],                kodaira := -20 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a3

namespace C45_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -720, a6 := -7259 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a4

namespace C45_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90, a6 := 175 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 0, 2],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a5

namespace C45_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -45, a6 := -104 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a6

namespace C45_a7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := -5 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a7

namespace C45_a8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 315, a6 := 1066 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 45 := by decide +kernel
theorem level_formula : wildLevel equation data = 45 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (45 : Nat) = 45 := by decide +kernel
end C45_a8

namespace C48_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -384, a6 := 2772 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 48 := by decide +kernel
theorem level_formula : wildLevel equation data = 48 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (48 : Nat) = 48 := by decide +kernel
end C48_a1

namespace C48_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -64, a6 := -220 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 48 := by decide +kernel
theorem level_formula : wildLevel equation data = 48 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (48 : Nat) = 48 := by decide +kernel
end C48_a2

namespace C48_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -24, a6 := 36 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 48 := by decide +kernel
theorem level_formula : wildLevel equation data = 48 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (48 : Nat) = 48 := by decide +kernel
end C48_a3

namespace C48_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 48 := by decide +kernel
theorem level_formula : wildLevel equation data = 48 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (48 : Nat) = 48 := by decide +kernel
end C48_a4

namespace C48_a5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 48 := by decide +kernel
theorem level_formula : wildLevel equation data = 48 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (48 : Nat) = 48 := by decide +kernel
end C48_a5

namespace C48_a6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 180 }
def data : WildData := { atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 48 := by decide +kernel
theorem level_formula : wildLevel equation data = 48 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (48 : Nat) = 48 := by decide +kernel
end C48_a6

namespace C52_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := -3 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 52 := by decide +kernel
theorem level_formula : wildLevel equation data = 52 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (52 : Nat) = 52 := by decide +kernel
end C52_a1

namespace C52_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -10 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 52 := by decide +kernel
theorem level_formula : wildLevel equation data = 52 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (52 : Nat) = 52 := by decide +kernel
end C52_a2

namespace C54_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -123, a6 := -667 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 54 := by decide +kernel
theorem level_formula : wildLevel equation data = 54 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (54 : Nat) = 54 := by decide +kernel
end C54_a1

namespace C54_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 3 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 54 := by decide +kernel
theorem level_formula : wildLevel equation data = 54 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (54 : Nat) = 54 := by decide +kernel
end C54_a2

namespace C54_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 12, a6 := 8 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 54 := by decide +kernel
theorem level_formula : wildLevel equation data = 54 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (54 : Nat) = 54 := by decide +kernel
end C54_a3

namespace C54_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := -53 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 54 := by decide +kernel
theorem level_formula : wildLevel equation data = 54 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (54 : Nat) = 54 := by decide +kernel
end C54_b1

namespace C54_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := 29 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 54 := by decide +kernel
theorem level_formula : wildLevel equation data = 54 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (54 : Nat) = 54 := by decide +kernel
end C54_b2

namespace C54_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1, a6 := -1 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 54 := by decide +kernel
theorem level_formula : wildLevel equation data = 54 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (54 : Nat) = 54 := by decide +kernel
end C54_b3

namespace C56_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := 1990 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 56 := by decide +kernel
theorem level_formula : wildLevel equation data = 56 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (56 : Nat) = 56 := by decide +kernel
end C56_a1

namespace C56_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := -138 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 56 := by decide +kernel
theorem level_formula : wildLevel equation data = 56 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (56 : Nat) = 56 := by decide +kernel
end C56_a2

namespace C56_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := 30 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 56 := by decide +kernel
theorem level_formula : wildLevel equation data = 56 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (56 : Nat) = 56 := by decide +kernel
end C56_a3

namespace C56_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 2 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 56 := by decide +kernel
theorem level_formula : wildLevel equation data = 56 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (56 : Nat) = 56 := by decide +kernel
end C56_a4

namespace C56_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -40, a6 := -84 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 56 := by decide +kernel
theorem level_formula : wildLevel equation data = 56 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (56 : Nat) = 56 := by decide +kernel
end C56_b1

namespace C56_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 56 := by decide +kernel
theorem level_formula : wildLevel equation data = 56 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (56 : Nat) = 56 := by decide +kernel
end C56_b2

namespace C63_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7056, a6 := 229905 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 63 := by decide +kernel
theorem level_formula : wildLevel equation data = 63 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (63 : Nat) = 63 := by decide +kernel
end C63_a1

namespace C63_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -441, a6 := 3672 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 63 := by decide +kernel
theorem level_formula : wildLevel equation data = 63 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (63 : Nat) = 63 := by decide +kernel
end C63_a2

namespace C63_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -351, a6 := -2430 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 1, 1, 0, 1, 2, 0],                kodaira := -12 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 63 := by decide +kernel
theorem level_formula : wildLevel equation data = 63 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (63 : Nat) = 63 := by decide +kernel
end C63_a3

namespace C63_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -306, a6 := 5859 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 63 := by decide +kernel
theorem level_formula : wildLevel equation data = 63 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (63 : Nat) = 63 := by decide +kernel
end C63_a4

namespace C63_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -36, a6 := 27 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 2, 0],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 63 := by decide +kernel
theorem level_formula : wildLevel equation data = 63 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (63 : Nat) = 63 := by decide +kernel
end C63_a5

namespace C63_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 9, a6 := 0 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 63 := by decide +kernel
theorem level_formula : wildLevel equation data = 63 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (63 : Nat) = 63 := by decide +kernel
end C63_a6

namespace C64_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -44, a6 := -112 }
def data : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 0, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 64 := by decide +kernel
theorem level_formula : wildLevel equation data = 64 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (64 : Nat) = 64 := by decide +kernel
end C64_a1

namespace C64_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -44, a6 := 112 }
def data : WildData := { atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [0, 1, 1, 0],              kodaira := -9 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 64 := by decide +kernel
theorem level_formula : wildLevel equation data = 64 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (64 : Nat) = 64 := by decide +kernel
end C64_a2

namespace C64_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 64 := by decide +kernel
theorem level_formula : wildLevel equation data = 64 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (64 : Nat) = 64 := by decide +kernel
end C64_a3

namespace C64_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 64 := by decide +kernel
theorem level_formula : wildLevel equation data = 64 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (64 : Nat) = 64 := by decide +kernel
end C64_a4

namespace C72_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3459, a6 := 78302 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 72 := by decide +kernel
theorem level_formula : wildLevel equation data = 72 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (72 : Nat) = 72 := by decide +kernel
end C72_a1

namespace C72_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -579, a6 := -5362 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 72 := by decide +kernel
theorem level_formula : wildLevel equation data = 72 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (72 : Nat) = 72 := by decide +kernel
end C72_a2

namespace C72_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -219, a6 := 1190 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 1, 0],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 72 := by decide +kernel
theorem level_formula : wildLevel equation data = 72 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (72 : Nat) = 72 := by decide +kernel
end C72_a3

namespace C72_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := -70 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 72 := by decide +kernel
theorem level_formula : wildLevel equation data = 72 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (72 : Nat) = 72 := by decide +kernel
end C72_a4

namespace C72_a5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 6, a6 := -7 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 72 := by decide +kernel
theorem level_formula : wildLevel equation data = 72 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (72 : Nat) = 72 := by decide +kernel
end C72_a5

namespace C72_a6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 141, a6 := 4718 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := some { r := 1,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 0, 2, 0, 2, 0],                kodaira := -12 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 72 := by decide +kernel
theorem level_formula : wildLevel equation data = 72 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (72 : Nat) = 72 := by decide +kernel
end C72_a6

namespace C76_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -21, a6 := -31 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 76 := by decide +kernel
theorem level_formula : wildLevel equation data = 76 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (76 : Nat) = 76 := by decide +kernel
end C76_a1

namespace C80_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -107, a6 := 426 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_a1

namespace C80_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := 6 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_a2

namespace C80_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := -1 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_a3

namespace C80_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 13, a6 := 34 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_a4

namespace C80_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -41, a6 := 116 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_b1

namespace C80_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -36, a6 := 140 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_b2

namespace C80_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_b3

namespace C80_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := -4 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 80 := by decide +kernel
theorem level_formula : wildLevel equation data = 80 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (80 : Nat) = 80 := by decide +kernel
end C80_b4

namespace C84_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -36, a6 := -72 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 84 := by decide +kernel
theorem level_formula : wildLevel equation data = 84 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (84 : Nat) = 84 := by decide +kernel
end C84_a1

namespace C84_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := -2 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 84 := by decide +kernel
theorem level_formula : wildLevel equation data = 84 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (84 : Nat) = 84 := by decide +kernel
end C84_a2

namespace C84_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1828, a6 := -30700 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 84 := by decide +kernel
theorem level_formula : wildLevel equation data = 84 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (84 : Nat) = 84 := by decide +kernel
end C84_b1

namespace C84_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -113, a6 := -516 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 84 := by decide +kernel
theorem level_formula : wildLevel equation data = 84 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (84 : Nat) = 84 := by decide +kernel
end C84_b2

namespace C84_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := -28 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 84 := by decide +kernel
theorem level_formula : wildLevel equation data = 84 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (84 : Nat) = 84 := by decide +kernel
end C84_b3

namespace C84_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 7, a6 := 0 }
def data : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 84 := by decide +kernel
theorem level_formula : wildLevel equation data = 84 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (84 : Nat) = 84 := by decide +kernel
end C84_b4

namespace C88_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 4 }
def data : WildData := { atTwo := some { r := 0, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 88 := by decide +kernel
theorem level_formula : wildLevel equation data = 88 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (88 : Nat) = 88 := by decide +kernel
end C88_a1

namespace C90_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1149, a6 := -14707 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_a1

namespace C90_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -69, a6 := -235 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_a2

namespace C90_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := 18 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_a3

namespace C90_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 6, a6 := 0 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_a4

namespace C90_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -218, a6 := -269 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_b1

namespace C90_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -128, a6 := 587 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_b2

namespace C90_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -8, a6 := 11 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_b3

namespace C90_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 52, a6 := -53 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_b4

namespace C90_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -48002, a6 := 4059929 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 1, 0],                kodaira := -8 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c1

namespace C90_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -4082, a6 := 14681 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c2

namespace C90_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3002, a6 := 63929 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0],                kodaira := -6 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c3

namespace C90_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2597, a6 := -50281 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c4

namespace C90_c5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -617, a6 := 5231 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 1, 0, 1, 2, 2, 1, 0, 2, 2, 1],                kodaira := -16 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c5

namespace C90_c6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -167, a6 := -709 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 1, 2, 0, 2],                kodaira := -10 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c6

namespace C90_c7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -122, a6 := 1721 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c7

namespace C90_c8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 13, a6 := -61 }
def data : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 1],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 90 := by decide +kernel
theorem level_formula : wildLevel equation data = 90 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (90 : Nat) = 90 := by decide +kernel
end C90_c8

namespace C92_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 1 }
def data : WildData := { atTwo := some { r := 1, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 92 := by decide +kernel
theorem level_formula : wildLevel equation data = 92 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (92 : Nat) = 92 := by decide +kernel
end C92_a1

namespace C92_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -18, a6 := -43 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 92 := by decide +kernel
theorem level_formula : wildLevel equation data = 92 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (92 : Nat) = 92 := by decide +kernel
end C92_b1

namespace C92_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 1 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 92 := by decide +kernel
theorem level_formula : wildLevel equation data = 92 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (92 : Nat) = 92 := by decide +kernel
end C92_b2

namespace C96_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -32, a6 := -60 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_a1

namespace C96_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -17, a6 := 33 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 0,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_a2

namespace C96_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_a3

namespace C96_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -8 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_a4

namespace C96_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -32, a6 := 60 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_b1

namespace C96_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -17, a6 := -33 }
def data : WildData := { atTwo := some { r := 1,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_b2

namespace C96_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := 0 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_b3

namespace C96_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 8, a6 := 8 }
def data : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 96 := by decide +kernel
theorem level_formula : wildLevel equation data = 96 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (96 : Nat) = 96 := by decide +kernel
end C96_b4

namespace C99_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -17, a6 := 30 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_a1

namespace C99_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := 0 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (-1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (-1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_a2

namespace C99_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1319, a6 := -18084 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 1],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_b1

namespace C99_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -104, a6 := -102 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [1, 1, 2, 0, 2],                kodaira := -10 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_b2

namespace C99_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -59, a6 := 186 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 2,                quadraticRoot := 0,                chain := [0, 0],                kodaira := -7 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_b3

namespace C99_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 391, a6 := -1092 }
def data : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 0,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [2, 2, 1, 0, 2, 2, 1, 0, 2, 2, 1],                kodaira := -16 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_b4

namespace C99_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -150, a6 := -667 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_c1

namespace C99_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15, a6 := 8 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 2,                chain := [],                kodaira := -3 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_c2

namespace C99_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -70383, a6 := 7187035 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_d1

namespace C99_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -93, a6 := 625 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_d2

namespace C99_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := -5 }
def data : WildData := { atTwo := none,   atThree := some { r := 1,                s := 0,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -1 } }
theorem valid : data.Valid equation := by decide +kernel
theorem level_fast : wildLevelFast equation data = 99 := by decide +kernel
theorem level_formula : wildLevel equation data = 99 :=
  (wildLevel_eq_fast equation data).trans level_fast
theorem sign_fast : wildSignFast equation data = (1 : Int) := by decide +kernel
theorem sign_formula : wildSign equation data = (1 : Int) :=
  (wildSign_eq_fast equation data valid).trans sign_fast
theorem conductor_reference_match : (99 : Nat) = 99 := by decide +kernel
end C99_d3

def certificateCount : Nat := 492
end VerifiedLcalc.EllipticCurve.WildExpandedExamples
