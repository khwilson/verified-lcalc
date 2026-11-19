module

public import VerifiedLcalc.EllipticCurve.ReductionArithmetic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve.AdditiveExamples

namespace C20_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -41, a6 := -116 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C20_a1

namespace C20_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -36, a6 := -140 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C20_a2

namespace C20_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C20_a3

namespace C20_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 4, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C20_a4

namespace C24_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -384, a6 := -2772 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C24_a1

namespace C24_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -64, a6 := 220 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C24_a2

namespace C24_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -24, a6 := -36 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C24_a3

namespace C24_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C24_a4

namespace C24_a5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 1, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C24_a5

namespace C24_a6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 16, a6 := -180 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C24_a6

namespace C27_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -270, a6 := -1708 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C27_a1

namespace C27_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -30, a6 := 63 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C27_a2

namespace C27_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -7 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C27_a3

namespace C27_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 0 }
def witness : MinimalityWitness := { primes := [3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C27_a4

namespace C32_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -14 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C32_a1

namespace C32_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := 14 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C32_a2

namespace C32_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C32_a3

namespace C32_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 4, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C32_a4

namespace C36_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -135, a6 := -594 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C36_a1

namespace C36_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -15, a6 := 22 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C36_a2

namespace C36_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -27 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C36_a3

namespace C36_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C36_a4

namespace C40_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -107, a6 := -426 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C40_a1

namespace C40_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := -6 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C40_a2

namespace C40_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C40_a3

namespace C40_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 13, a6 := -34 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
theorem additive_factor_2 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 2).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 2).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 2
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C40_a4

end VerifiedLcalc.EllipticCurve.AdditiveExamples
