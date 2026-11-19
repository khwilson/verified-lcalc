module

public import VerifiedLcalc.EllipticCurve.ReductionArithmetic

@[expose] public section
namespace VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples

namespace C100_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1033, a6 := -12438 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C100_a1

namespace C100_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -908, a6 := -15688 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C100_a2

namespace C100_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -33, a6 := 62 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C100_a3

namespace C100_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 92, a6 := 312 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C100_a4

namespace C104_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -16, a6 := -32 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13] }
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
end C104_a1

namespace C108_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -108 }
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
end C108_a1

namespace C108_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 4 }
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
end C108_a2

namespace C112_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -40, a6 := 84 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
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
end C112_a1

namespace C112_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
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
end C112_a2

namespace C112_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := -1990 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
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
end C112_b1

namespace C112_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := 138 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7] }
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
end C112_b2

namespace C112_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := -30 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
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
end C112_b3

namespace C112_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 7] }
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
end C112_b4

namespace C116_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4831, a6 := -129242 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 29] }
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
end C116_a1

namespace C116_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 29] }
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
end C116_b1

namespace C116_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 36, a6 := -76 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 29, 29, 29] }
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
end C116_b2

namespace C116_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := 14 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 29] }
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
end C116_c1

namespace C116_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 24 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 29, 29] }
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
end C116_c2

namespace C117_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -626, a6 := 6180 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
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
end C117_a1

namespace C117_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -176, a6 := -768 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13] }
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
end C117_a2

namespace C117_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -41, a6 := 96 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
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
end C117_a3

namespace C117_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := 6 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 13] }
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
end C117_a4

namespace C120_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -216, a6 := -1296 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5] }
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
end C120_a1

namespace C120_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -136, a6 := 560 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5] }
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
end C120_a2

namespace C120_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -16, a6 := -16 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5] }
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
end C120_a3

namespace C120_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 4, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5] }
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
end C120_a4

namespace C120_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3200, a6 := -70752 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5] }
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
end C120_b1

namespace C120_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -200, a6 := -1152 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 5] }
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
end C120_b2

namespace C120_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -80, a6 := -2400 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
end C120_b3

namespace C120_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -20, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5] }
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
end C120_b4

namespace C120_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -15, a6 := 18 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5] }
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
end C120_b5

namespace C120_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 80, a6 := 80 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C120_b6

namespace C121_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -305, a6 := 7888 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_a1

namespace C121_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -30, a6 := -76 }
def witness : MinimalityWitness := { primes := [11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_a2

namespace C121_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -887, a6 := -10143 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_b1

namespace C121_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -7, a6 := 10 }
def witness : MinimalityWitness := { primes := [11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_b2

namespace C121_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -3632, a6 := 82757 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_c1

namespace C121_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -2, a6 := -7 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_c2

namespace C121_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -946260, a6 := 354609639 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_d1

namespace C121_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -1250, a6 := 31239 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_d2

namespace C121_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -40, a6 := -221 }
def witness : MinimalityWitness := { primes := [11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C121_d3

namespace C124_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
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
end C124_a1

namespace C124_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 18, a6 := -11 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31, 31, 31] }
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
end C124_a2

namespace C124_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -17, a6 := -27 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
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
end C124_b1

namespace C126_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -12096, a6 := -509036 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C126_a1

namespace C126_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -8226, a6 := 286474 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
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
end C126_a2

namespace C126_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -936, a6 := -3668 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
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
end C126_a3

namespace C126_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -756, a6 := -7808 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C126_a4

namespace C126_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -36, a6 := -176 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C126_a5

namespace C126_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3474, a6 := -31010 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C126_a6

namespace C126_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -24575, a6 := 1488935 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C126_b1

namespace C126_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1535, a6 := 23591 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }
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
end C126_b2

namespace C126_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -320, a6 := 1883 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7] }
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
end C126_b3

namespace C126_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -95, a6 := -331 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C126_b4

namespace C126_b5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := -7 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 7] }
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
end C126_b5

namespace C126_b6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 40, a6 := 155 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
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
end C126_b6

namespace C128_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := 7 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
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
end C128_a1

namespace C128_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2] }
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
end C128_a2

namespace C128_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := -2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2] }
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
end C128_b1

namespace C128_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := -7 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
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
end C128_c1

namespace C128_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 1, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2] }
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
end C128_c2

namespace C128_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2] }
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
end C128_d1

namespace C132_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1292, a6 := 18312 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 11, 11] }
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
end C132_a1

namespace C132_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -77, a6 := 330 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C132_a2

namespace C132_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -12, a6 := -12 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 11, 11] }
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
end C132_b1

namespace C132_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 11] }
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
end C132_b2

namespace C135_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 4 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 5] }
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
end C135_a1

namespace C135_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := -115 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
end C135_b1

namespace C136_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 17] }
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
end C136_a1

namespace C136_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 16 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
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
end C136_a2

namespace C136_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -48, a6 := 140 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
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
end C136_b1

namespace C136_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -8, a6 := -4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17] }
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
end C136_b2

namespace C140_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -805, a6 := -9065 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7, 7, 7] }
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
end C140_a1

namespace C140_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -25 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 7] }
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
end C140_a2

namespace C140_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 32, a6 := 212 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7, 7, 7, 7, 7] }
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
end C140_b1

namespace C144_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -135, a6 := 594 }
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
end C144_a1

namespace C144_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -15, a6 := -22 }
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
end C144_a2

namespace C144_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -1 }
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
end C144_a3

namespace C144_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 27 }
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
end C144_a4

namespace C144_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3459, a6 := -78302 }
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
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C144_b1

namespace C144_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -579, a6 := 5362 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
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
end C144_b2

namespace C144_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -219, a6 := -1190 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C144_b3

namespace C144_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := 70 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C144_b4

namespace C144_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 6, a6 := 7 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
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
end C144_b5

namespace C144_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 141, a6 := -4718 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C144_b6

namespace C147_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -38417, a6 := 2882228 }
def witness : MinimalityWitness := { primes := [3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_a1

namespace C147_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2402, a6 := 44246 }
def witness : MinimalityWitness := { primes := [3, 3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_a2

namespace C147_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1912, a6 := -32782 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_a3

namespace C147_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1667, a6 := 72764 }
def witness : MinimalityWitness := { primes := [3, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_a4

namespace C147_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -197, a6 := 146 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_a5

namespace C147_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 48, a6 := 48 }
def witness : MinimalityWitness := { primes := [3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_a6

namespace C147_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -912, a6 := 10919 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_b1

namespace C147_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -2, a6 := -1 }
def witness : MinimalityWitness := { primes := [3, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_b2

namespace C147_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -44704, a6 := -3655907 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_c1

namespace C147_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -114, a6 := 473 }
def witness : MinimalityWitness := { primes := [3, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C147_c2

namespace C148_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 37] }
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
end C148_a1

namespace C150_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -20700, a6 := 1134000 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_a1

namespace C150_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1325, a6 := -19125 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_a2

namespace C150_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -700, a6 := 34000 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_a3

namespace C150_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -75, a6 := -375 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_a4

namespace C150_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -133338, a6 := -18795969 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b1

namespace C150_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -11338, a6 := -67969 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b2

namespace C150_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -8338, a6 := -295969 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b3

namespace C150_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -7213, a6 := 232781 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b4

namespace C150_b5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1713, a6 := -24219 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b5

namespace C150_b6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -463, a6 := 3281 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b6

namespace C150_b7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -338, a6 := -7969 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b7

namespace C150_b8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 37, a6 := 281 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_b8

namespace C150_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -828, a6 := 9072 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_c1

namespace C150_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -53, a6 := -153 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_c2

namespace C150_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -28, a6 := 272 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_c3

namespace C150_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := -3 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C150_c4

namespace C152_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 3 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 19] }
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
end C152_a1

namespace C152_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := -16 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 19] }
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
end C152_b1

namespace C153_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 2 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 17] }
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
end C153_a1

namespace C153_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -534, a6 := 4752 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 17, 17, 17] }
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
end C153_b1

namespace C153_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 27 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
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
end C153_b2

namespace C153_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -816, a6 := 9179 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 17] }
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
end C153_c1

namespace C153_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -51, a6 := 152 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 17, 17] }
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
end C153_c2

namespace C153_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := -1 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 17] }
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
end C153_c3

namespace C153_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := 377 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 17, 17, 17, 17] }
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
end C153_c4

namespace C153_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := -61 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
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
end C153_d1

namespace C156_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := -24 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13] }
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
end C156_a1

namespace C156_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 6 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13] }
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
end C156_a2

namespace C156_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -748, a6 := -7564 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 13, 13, 13, 13, 13, 13] }
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
end C156_b1

namespace C156_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -733, a6 := -7888 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 13, 13, 13] }
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
end C156_b2

namespace C156_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -148, a6 := 644 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 13, 13] }
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
end C156_b3

namespace C156_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := -4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 13] }
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
end C156_b4

namespace C160_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -6, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5] }
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
end C160_a1

namespace C160_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 15 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
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
end C160_a2

namespace C160_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -6, a6 := -4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 5] }
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
end C160_b1

namespace C160_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := -15 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
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
end C160_b2

namespace C162_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -6, a6 := 8 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3] }
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
end C162_a1

namespace C162_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 39, a6 := -19 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C162_a2

namespace C162_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1077, a6 := 13877 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3] }
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
end C162_b1

namespace C162_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -852, a6 := 19664 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C162_b2

namespace C162_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -42, a6 := -100 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C162_b3

namespace C162_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 3, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3] }
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
end C162_b4

namespace C162_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -95, a6 := -697 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C162_c2

namespace C162_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 5 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3] }
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
end C162_c3

namespace C162_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C162_d2

namespace C168_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4032, a6 := 99900 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7] }
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
end C168_a1

namespace C168_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -392, a6 := -228 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C168_a2

namespace C168_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -252, a6 := 1620 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C168_a3

namespace C168_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -7, a6 := 52 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7, 7, 7, 7] }
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
end C168_a4

namespace C168_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -152, a6 := 672 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 7] }
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
end C168_b1

namespace C168_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -12, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7] }
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
end C168_b2

namespace C168_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7, a6 := -10 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7] }
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
end C168_b3

namespace C168_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 48, a6 := 48 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 7, 7, 7, 7] }
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
end C168_b4

namespace C171_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -914, a6 := -10402 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 19] }
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
end C171_a1

namespace C171_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -59, a6 := -142 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 19, 19] }
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
end C171_a2

namespace C171_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := 20 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 19] }
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
end C171_a3

namespace C171_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 76, a6 := -790 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 19, 19, 19, 19] }
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
end C171_a4

namespace C171_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -6924, a6 := 221760 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
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
end C171_b1

namespace C171_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -84, a6 := 315 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19, 19, 19] }
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
end C171_b2

namespace C171_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 6, a6 := 0 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 19] }
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
end C171_b3

namespace C171_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -39513, a6 := 3023145 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 19, 19, 19, 19, 19] }
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
end C171_c1

namespace C171_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 177, a6 := 1035 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 19] }
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
end C171_c2

namespace C171_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -21, a6 := -41 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 19] }
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
end C171_d1

namespace C172_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -13, a6 := 15 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43] }
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
end C172_a1

namespace C172_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 67, a6 := 79 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 43, 43, 43] }
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
end C172_a2

namespace C175_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -148, a6 := 748 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_a1

namespace C175_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 2, a6 := -2 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_a2

namespace C175_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3283, a6 := -74657 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_b1

namespace C175_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -33, a6 := 93 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_b2

namespace C175_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 217, a6 := -282 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_b3

namespace C175_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -3708, a6 := 86119 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_c1

namespace C175_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 42, a6 := -131 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C175_c2

namespace C176_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -77, a6 := 289 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11] }
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
end C176_a1

namespace C176_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
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
end C176_a2

namespace C176_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := -4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
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
end C176_c1

namespace C180_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -372, a6 := 2761 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C180_a1

namespace C180_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -327, a6 := 3454 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }
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
end C180_a2

namespace C180_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := -11 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5] }
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
end C180_a3

namespace C180_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 33, a6 := -74 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5] }
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
end C180_a4

namespace C184_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
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
end C184_a1

namespace C184_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 5 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
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
end C184_b1

namespace C184_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -35, a6 := 62 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 23, 23] }
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
end C184_c1

namespace C184_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 5, a6 := 6 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 23] }
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
end C184_c2

namespace C184_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -55, a6 := -157 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
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
end C184_d1

namespace C189_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := 0 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 7] }
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
end C189_a1

namespace C189_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3834, a6 := -91375 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C189_b1

namespace C189_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -54, a6 := -88 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
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
end C189_b2

namespace C189_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -24, a6 := 45 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 7] }
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
end C189_b3

namespace C189_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -426, a6 := 3384 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 7] }
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
end C189_c1

namespace C189_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -216, a6 := -1222 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C189_c2

namespace C189_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -6, a6 := 3 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 7, 7, 7] }
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
end C189_c3

namespace C189_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -27, a6 := -7 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C189_d1

namespace C192_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -129, a6 := 609 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C192_a1

namespace C192_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -9, a6 := 9 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
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
end C192_a2

namespace C192_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := -2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3] }
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
end C192_a3

namespace C192_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 31, a6 := 33 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C192_a4

namespace C192_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1537, a6 := 23713 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
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
end C192_b1

namespace C192_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -257, a6 := -1503 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C192_b2

namespace C192_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -97, a6 := 385 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C192_b3

namespace C192_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -17, a6 := -15 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
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
end C192_b4

namespace C192_b5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := -3 }
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
end C192_b5

namespace C192_b6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 63, a6 := 1377 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C192_b6

namespace C192_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -129, a6 := -609 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C192_c1

namespace C192_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := -9 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
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
end C192_c2

namespace C192_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := 2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3] }
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
end C192_c3

namespace C192_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 31, a6 := -33 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C192_c4

namespace C192_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1537, a6 := -23713 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
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
end C192_d1

namespace C192_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -257, a6 := 1503 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C192_d2

namespace C192_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -97, a6 := -385 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C192_d3

namespace C192_d4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -17, a6 := 15 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }
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
end C192_d4

namespace C192_d5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := 3 }
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
end C192_d5

namespace C192_d6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 63, a6 := -1377 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C192_d6

namespace C196_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -142, a6 := 701 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
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
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C196_a1

namespace C196_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7] }
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
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C196_a2

namespace C196_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -6974, a6 := -226507 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7] }
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
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C196_b1

namespace C196_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -114, a6 := -127 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7] }
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
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C196_b2

namespace C198_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3168, a6 := 69430 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C198_a1

namespace C198_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -198, a6 := 1120 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C198_a2

namespace C198_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -108, a6 := 2074 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11] }
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
end C198_a3

namespace C198_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -18, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C198_a4

namespace C198_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -9222, a6 := -338572 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C198_b1

namespace C198_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -582, a6 := -5068 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C198_b2

namespace C198_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -147, a6 := -135 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 11, 11, 11, 11, 11, 11] }
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
end C198_b3

namespace C198_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -87, a6 := 333 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 11, 11, 11] }
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
end C198_b4

namespace C198_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90585, a6 := 10516473 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11, 11] }
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
end C198_c1

namespace C198_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90495, a6 := 10538343 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] }
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
end C198_c2

namespace C198_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -405, a6 := -2187 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C198_c3

namespace C198_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1035, a6 := -15147 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C198_c4

namespace C198_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1325, a6 := 4969 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11, 11, 11] }
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
end C198_d1

namespace C198_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1025, a6 := 12881 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 11, 11] }
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
end C198_d2

namespace C198_d3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -785, a6 := -8207 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11] }
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
end C198_d3

namespace C198_d4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -65, a6 := 209 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 11] }
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
end C198_d4

namespace C198_e1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -725, a6 := 7661 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11] }
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
end C198_e1

namespace C198_e2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -365, a6 := 15005 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11, 11, 11] }
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
end C198_e2

namespace C198_e3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -50, a6 := -115 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C198_e3

namespace C198_e4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 40, a6 := -547 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C198_e4

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

namespace C200_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 125, a6 := -1250 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_a1

namespace C200_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := 48 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_b1

namespace C200_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := -2 }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_b2

namespace C200_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2675, a6 := -53250 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_c1

namespace C200_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -175, a6 := -750 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_c2

namespace C200_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -50, a6 := 125 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_c3

namespace C200_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 325, a6 := -4250 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_c4

namespace C200_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -708, a6 := 7412 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_d1

namespace C200_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -83, a6 := -88 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_d2

namespace C200_e1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 5, a6 := -10 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C200_e1

namespace C204_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1621, a6 := -24623 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 17] }
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
end C204_a1

namespace C204_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -5, a6 := -9 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 17] }
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
end C204_b1

namespace C207_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -140, a6 := 668 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 23, 23] }
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
end C207_a1

namespace C207_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := 20 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 23] }
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
end C207_a2

namespace C208_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 32 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13] }
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
end C208_b1

namespace C208_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 3 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 13] }
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
end C208_c1

namespace C208_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 10 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 13, 13] }
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
end C208_c2

namespace C212_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 53] }
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
end C212_a1

namespace C212_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -17, a6 := -22 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 53] }
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
end C212_b1

namespace C212_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := -40 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 53, 53] }
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
end C212_b2

namespace C216_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 20 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
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
end C216_a1

namespace C216_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3, a6 := -34 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
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
end C216_b1

namespace C216_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -27, a6 := 918 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C216_c1

namespace C216_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -108, a6 := -540 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C216_d1

namespace C220_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7100, a6 := -232652 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 11, 11, 11] }
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
end C220_a1

namespace C220_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -445, a6 := -3720 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 11, 11, 11, 11, 11, 11] }
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
end C220_a2

namespace C220_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -100, a6 := -252 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 11] }
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
end C220_a3

namespace C220_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -45, a6 := 100 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 5, 5, 11, 11] }
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
end C220_a4

namespace C220_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -60, a6 := 200 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 11] }
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
end C220_b1

namespace C220_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -5, a6 := 2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 11, 11] }
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
end C220_b2

namespace C224_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := -8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
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
end C224_a1

namespace C224_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7] }
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
end C224_a2

namespace C224_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -8, a6 := 8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
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
end C224_b1

namespace C224_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 2, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7] }
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
end C224_b2

namespace C225_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -75, a6 := 256 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_a1

namespace C225_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 375, a6 := -12344 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_a2

namespace C225_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -486005, a6 := 130530872 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b1

namespace C225_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -30380, a6 := 2044622 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b2

namespace C225_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -24755, a6 := 2820872 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b3

namespace C225_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -18005, a6 := -925378 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b4

namespace C225_b5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2255, a6 := 19622 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b5

namespace C225_b6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1130, a6 := -14128 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b6

namespace C225_b7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -5, a6 := -628 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b7

namespace C225_b8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 7870, a6 := 141122 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_b8

namespace C225_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -34 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_c1

namespace C225_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 1 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_c2

namespace C225_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -4219 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_d1

namespace C225_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 156 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_d2

namespace C225_e1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -1875, a6 := 32031 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_e1

namespace C225_e2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 15, a6 := -99 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C225_e2

namespace C228_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 9 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 19] }
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
end C228_a1

namespace C228_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -92, a6 := 360 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 19] }
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
end C228_b1

namespace C228_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := 18 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 19, 19] }
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
end C228_b2

namespace C232_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 29] }
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
end C232_a1

namespace C232_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -80, a6 := -304 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 29] }
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
end C232_b1

namespace C234_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -63, a6 := 209 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 13, 13] }
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
end C234_a1

namespace C234_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 5 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 13] }
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
end C234_a2

namespace C234_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1914, a6 := 35846 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13, 13, 13, 13] }
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
end C234_b1

namespace C234_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := -64 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 13] }
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
end C234_b2

namespace C234_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -186656, a6 := -30992493 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13, 13, 13, 13] }
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
end C234_c1

namespace C234_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -21056, a6 := 404115 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
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
end C234_c2

namespace C234_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11696, a6 := -479469 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
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
end C234_c3

namespace C234_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -176, a6 := -18669 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
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
end C234_c4

namespace C234_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -569, a6 := -5075 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13, 13] }
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
end C234_d1

namespace C234_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := -107 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 13] }
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
end C234_d2

namespace C234_e1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -4136, a6 := 103403 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 13] }
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
end C234_e1

namespace C234_e2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -41, a6 := 209 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 13, 13, 13] }
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
end C234_e2

namespace C234_e3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 4, a6 := -7 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 13] }
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
end C234_e3

namespace C236_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 59] }
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
end C236_a1

namespace C236_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -9, a6 := 8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 59] }
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
end C236_b1

namespace C236_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 31, a6 := 68 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 59, 59, 59] }
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
end C236_b2

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

namespace C240_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -216, a6 := 1296 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5] }
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
end C240_a1

namespace C240_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -136, a6 := -560 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5] }
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
end C240_a2

namespace C240_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -16, a6 := 16 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5] }
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
end C240_a3

namespace C240_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5] }
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
end C240_a4

namespace C240_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -3200, a6 := 70752 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5] }
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
end C240_c1

namespace C240_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -200, a6 := 1152 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 5, 5] }
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
end C240_c2

namespace C240_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -80, a6 := 2400 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
end C240_c3

namespace C240_c4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -20, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5] }
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
end C240_c4

namespace C240_c5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -15, a6 := -18 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5] }
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
end C240_c5

namespace C240_c6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 80, a6 := -80 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C240_c6

namespace C242_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -6295, a6 := -197958 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C242_a1

namespace C242_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 360, a6 := -970 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 11, 11, 11, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C242_a2

namespace C242_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := -52, a6 := 144 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C242_b1

namespace C242_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 0, a4 := 3, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_11 : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
theorem additive_factor_11 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 11).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 11).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 11
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C242_b2

namespace C243_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -1 }
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
end C243_a1

namespace C243_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 20 }
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
end C243_a2

namespace C243_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 2 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3] }
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
end C243_b2

namespace C244_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 6 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 61] }
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
end C244_a1

namespace C245_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -7, a6 := 12 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C245_a1

namespace C245_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -343, a6 := -4202 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C245_b1

namespace C245_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -6435, a6 := 210006 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C245_c1

namespace C245_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -65, a6 := -204 }
def witness : MinimalityWitness := { primes := [5, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C245_c2

namespace C245_c3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 425, a6 := 433 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C245_c3

namespace C248_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 0, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
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
end C248_a1

namespace C248_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -32, a6 := -32 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 31, 31] }
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
end C248_b1

namespace C248_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 8, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 31] }
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
end C248_b2

namespace C248_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 31] }
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
end C248_c1

namespace C252_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -327, a6 := 2270 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C252_a1

namespace C252_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -12, a6 := 65 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C252_a2

namespace C252_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -16455, a6 := 812446 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
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
end C252_b1

namespace C252_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1020, a6 := 12913 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7] }
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
end C252_b2

namespace C252_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -255, a6 := 502 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C252_b3

namespace C252_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 60, a6 := 61 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C252_b4

namespace C256_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -3, a6 := 1 }
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
end C256_a2

namespace C256_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 0 }
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
end C256_b1

namespace C256_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 2, a6 := 0 }
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
end C256_c2

namespace C256_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -3, a6 := -1 }
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
end C256_d2

namespace C260_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -281, a6 := 1910 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 5, 13, 13] }
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
end C260_a1

namespace C260_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -276, a6 := 1976 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 13, 13, 13, 13] }
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
end C260_a2

namespace C264_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -472, a6 := 4108 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 11] }
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
end C264_a1

namespace C264_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -32, a6 := 60 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 11, 11] }
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
end C264_a2

namespace C264_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -12, a6 := -12 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 11] }
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
end C264_a3

namespace C264_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 88, a6 := 300 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11, 11, 11, 11] }
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
end C264_a4

namespace C264_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -704, a6 := 6960 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11] }
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
end C264_b1

namespace C264_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -104, a6 := -288 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11, 11, 11, 11] }
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
end C264_b2

namespace C264_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -44, a6 := 96 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 11, 11] }
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
end C264_b3

namespace C264_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 6 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 11] }
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
end C264_b4

namespace C264_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11] }
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
end C264_c1

namespace C264_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 32, a6 := 32 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 11, 11] }
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
end C264_c2

namespace C264_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8016, a6 := -278928 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C264_d1

namespace C264_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -7976, a6 := -281808 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C264_d2

namespace C268_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 3, a6 := -7 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 67] }
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
end C268_a1

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

namespace C270_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15, a6 := 35 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C270_a1

namespace C270_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 120, a6 := -424 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C270_a2

namespace C270_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -159, a6 := 813 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5] }
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
end C270_b1

namespace C270_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 66, a6 := 2708 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C270_b2

namespace C270_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1433, a6 := -20519 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C270_c1

namespace C270_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 7, a6 := -103 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5] }
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
end C270_c2

namespace C270_d1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 5] }
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
end C270_d1

namespace C270_d2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 13, a6 := 11 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C270_d2

namespace C272_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -48, a6 := -140 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
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
end C272_a1

namespace C272_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -8, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17] }
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
end C272_a2

namespace C272_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 17] }
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
end C272_c1

namespace C272_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 16, a6 := -16 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 17] }
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
end C272_c2

namespace C275_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1480, a6 := 22272 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_a1

namespace C275_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -730, a6 := -7228 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_a2

namespace C275_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -105, a6 := 272 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 5, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_a3

namespace C275_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 20, a6 := 22 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 5, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_a4

namespace C275_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -195508, a6 := -33338481 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_b1

namespace C275_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -258, a6 := -2981 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 11, 11, 11, 11, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_b2

namespace C275_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -8, a6 := 19 }
def witness : MinimalityWitness := { primes := [5, 5, 5, 5, 5, 5, 11] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C275_b3

namespace C280_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -412, a6 := 3316 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 7, 7, 7] }
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
end C280_a1

namespace C280_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 5 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 7] }
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
end C280_b1

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

namespace C44_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -77, a6 := -289 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11] }
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
end C44_a1

namespace C44_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
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
end C44_a2

namespace C45_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -19440, a6 := 1048135 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C45_a1

namespace C45_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1215, a6 := 16600 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
end C45_a2

namespace C45_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -990, a6 := 22765 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C45_a3

namespace C45_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -720, a6 := -7259 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5] }
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
end C45_a4

namespace C45_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90, a6 := 175 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
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
end C45_a5

namespace C45_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -45, a6 := -104 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
end C45_a6

namespace C45_a7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := -5 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 5] }
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
end C45_a7

namespace C45_a8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 315, a6 := 1066 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
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
end C45_a8

namespace C48_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -384, a6 := 2772 }
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
end C48_a1

namespace C48_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -64, a6 := -220 }
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
end C48_a2

namespace C48_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -24, a6 := 36 }
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
end C48_a3

namespace C48_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := -4 }
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
end C48_a4

namespace C48_a5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 0 }
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
end C48_a5

namespace C48_a6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 180 }
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
end C48_a6

namespace C49_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1822, a6 := 30393 }
def witness : MinimalityWitness := { primes := [7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C49_a1

namespace C49_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -107, a6 := 552 }
def witness : MinimalityWitness := { primes := [7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C49_a2

namespace C49_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -37, a6 := -78 }
def witness : MinimalityWitness := { primes := [7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C49_a3

namespace C49_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := -1 }
def witness : MinimalityWitness := { primes := [7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C49_a4

namespace C50_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -126, a6 := -552 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_a1

namespace C50_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -76, a6 := 298 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_a2

namespace C50_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1, a6 := -2 }
def witness : MinimalityWitness := { primes := [2, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_a3

namespace C50_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 549, a6 := -2202 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_a4

namespace C50_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -3138, a6 := -68969 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_b1

namespace C50_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -13, a6 := -219 }
def witness : MinimalityWitness := { primes := [2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_b2

namespace C50_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := -3, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_b3

namespace C50_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 1, a4 := 22, a6 := -9 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C50_b4

namespace C52_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := -3 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 13] }
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
end C52_a1

namespace C52_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -10 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 13, 13] }
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
end C52_a2

namespace C54_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -123, a6 := -667 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C54_a1

namespace C54_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 3 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3] }
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
end C54_a2

namespace C54_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 12, a6 := 8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C54_a3

namespace C54_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := -53 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C54_b1

namespace C54_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := 29 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }
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
end C54_b2

namespace C54_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1, a6 := -1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3] }
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
end C54_b3

namespace C56_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := 1990 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
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
end C56_a1

namespace C56_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := -138 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7] }
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
end C56_a2

namespace C56_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := 30 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
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
end C56_a3

namespace C56_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 7] }
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
end C56_a4

namespace C56_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -40, a6 := -84 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }
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
end C56_b1

namespace C56_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }
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
end C56_b2

namespace C63_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7056, a6 := 229905 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C63_a1

namespace C63_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -441, a6 := 3672 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }
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
end C63_a2

namespace C63_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -351, a6 := -2430 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C63_a3

namespace C63_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -306, a6 := 5859 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }
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
end C63_a4

namespace C63_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -36, a6 := 27 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }
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
end C63_a5

namespace C63_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 9, a6 := 0 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 7] }
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
end C63_a6

namespace C64_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -44, a6 := -112 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
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
end C64_a1

namespace C64_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -44, a6 := 112 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }
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
end C64_a2

namespace C64_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 0 }
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
end C64_a3

namespace C64_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 0 }
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
end C64_a4

namespace C72_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -3459, a6 := 78302 }
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
local instance prime_3 : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
theorem additive_factor_3 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 3).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 3).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 3
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C72_a1

namespace C72_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -579, a6 := -5362 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
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
end C72_a2

namespace C72_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -219, a6 := 1190 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C72_a3

namespace C72_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -39, a6 := -70 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C72_a4

namespace C72_a5
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 6, a6 := -7 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3] }
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
end C72_a5

namespace C72_a6
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 141, a6 := 4718 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }
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
end C72_a6

namespace C75_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := -208, a6 := -1256 }
def witness : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_a1

namespace C75_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 1, a4 := 2, a6 := 4 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_a2

namespace C75_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -54001, a6 := -4834477 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b1

namespace C75_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -3376, a6 := -75727 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b2

namespace C75_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2751, a6 := -104477 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b3

namespace C75_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2001, a6 := 34273 }
def witness : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b4

namespace C75_b5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -251, a6 := -727 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b5

namespace C75_b6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -126, a6 := 523 }
def witness : MinimalityWitness := { primes := [3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b6

namespace C75_b7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1, a6 := 23 }
def witness : MinimalityWitness := { primes := [3, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b7

namespace C75_b8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 0, a3 := 1, a4 := 874, a6 := -5227 }
def witness : MinimalityWitness := { primes := [3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_b8

namespace C75_c1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -8, a6 := -7 }
def witness : MinimalityWitness := { primes := [3, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_c1

namespace C75_c2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 42, a6 := 443 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_5 : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
theorem additive_factor_5 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 5).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 5).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 5
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C75_c2

namespace C76_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -21, a6 := -31 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 19] }
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
end C76_a1

namespace C80_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -107, a6 := 426 }
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
end C80_a1

namespace C80_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := 6 }
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
end C80_a2

namespace C80_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := -1 }
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
end C80_a3

namespace C80_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := 13, a6 := 34 }
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
end C80_a4

namespace C80_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -41, a6 := 116 }
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
end C80_b1

namespace C80_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -36, a6 := 140 }
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
end C80_b2

namespace C80_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := 0 }
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
end C80_b3

namespace C80_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 4, a6 := -4 }
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
end C80_b4

namespace C84_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -36, a6 := -72 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7] }
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
end C84_a1

namespace C84_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1, a6 := -2 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7] }
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
end C84_a2

namespace C84_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1828, a6 := -30700 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 7] }
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
end C84_b1

namespace C84_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -113, a6 := -516 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 7, 7, 7, 7, 7, 7] }
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
end C84_b2

namespace C84_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -28, a6 := -28 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 7] }
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
end C84_b3

namespace C84_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 7, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 7, 7] }
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
end C84_b4

namespace C88_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := 4 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }
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
end C88_a1

namespace C90_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1149, a6 := -14707 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
end C90_a1

namespace C90_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -69, a6 := -235 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C90_a2

namespace C90_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -24, a6 := 18 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 5, 5, 5, 5, 5, 5] }
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
end C90_a3

namespace C90_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 6, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 5, 5, 5] }
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
end C90_a4

namespace C90_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -218, a6 := -269 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }
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
end C90_b1

namespace C90_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -128, a6 := 587 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 5, 5] }
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
end C90_b2

namespace C90_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -8, a6 := 11 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 5] }
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
end C90_b3

namespace C90_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 52, a6 := -53 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C90_b4

namespace C90_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -48002, a6 := 4059929 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C90_c1

namespace C90_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -4082, a6 := 14681 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
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
end C90_c2

namespace C90_c3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3002, a6 := 63929 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5] }
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
end C90_c3

namespace C90_c4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2597, a6 := -50281 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }
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
end C90_c4

namespace C90_c5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -617, a6 := 5231 }
def witness : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C90_c5

namespace C90_c6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -167, a6 := -709 }
def witness : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }
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
end C90_c6

namespace C90_c7
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -122, a6 := 1721 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5] }
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
end C90_c7

namespace C90_c8
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 13, a6 := -61 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }
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
end C90_c8

namespace C92_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
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
end C92_a1

namespace C92_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -18, a6 := -43 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23, 23, 23] }
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
end C92_b1

namespace C92_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 2, a6 := 1 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 23] }
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
end C92_b2

namespace C96_a1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -32, a6 := -60 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C96_a1

namespace C96_a2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -17, a6 := 33 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C96_a2

namespace C96_a3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -2, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3] }
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
end C96_a3

namespace C96_a4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 8, a6 := -8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C96_a4

namespace C96_b1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -32, a6 := 60 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C96_b1

namespace C96_b2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -17, a6 := -33 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }
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
end C96_b2

namespace C96_b3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -2, a6 := 0 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3] }
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
end C96_b3

namespace C96_b4
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 8, a6 := 8 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }
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
end C96_b4

namespace C98_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -133795, a6 := 18781197 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C98_a1

namespace C98_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -8355, a6 := 291341 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C98_a2

namespace C98_a3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -1740, a6 := 22184 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C98_a3

namespace C98_a4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -515, a6 := -4717 }
def witness : MinimalityWitness := { primes := [2, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C98_a4

namespace C98_a5
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := -25, a6 := -111 }
def witness : MinimalityWitness := { primes := [2, 2, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C98_a5

namespace C98_a6
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := 1, a3 := 0, a4 := 220, a6 := 2192 }
def witness : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 7, 7, 7, 7, 7, 7, 7, 7, 7] }
theorem witness_valid : witness.Valid equation := by decide +kernel
theorem coefficients_correct (limit : ℕ) :
    modelCoefficients equation limit = (List.range limit).map
      (fun j => (weierstrass equation ℚ).LFunction (j + 1)) :=
  minimal_prefix equation (by decide +kernel) (minimal_of_witness equation witness witness_valid) limit
local instance prime_7 : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
theorem additive_factor_7 :
    ((weierstrass equation ℚ).baseChange ((rationalPlace 7).adicCompletion ℚ)).localPolynomial
      ((rationalPlace 7).adicCompletionIntegers ℚ) = 1 :=
  additive_localPolynomial equation (by decide +kernel) 7
    (minimal_of_witness equation witness witness_valid _) (by decide +kernel)
end C98_a6

namespace C99_a1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -17, a6 := 30 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 11, 11] }
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
end C99_a1

namespace C99_a2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := 0 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 11] }
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
end C99_a2

namespace C99_b1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1319, a6 := -18084 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11, 11, 11] }
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
end C99_b1

namespace C99_b2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -104, a6 := -102 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C99_b2

namespace C99_b3
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -59, a6 := 186 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C99_b3

namespace C99_b4
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 391, a6 := -1092 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C99_b4

namespace C99_c1
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -150, a6 := -667 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 11, 11] }
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
end C99_c1

namespace C99_c2
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -15, a6 := 8 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 11] }
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
end C99_c2

namespace C99_d1
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -70383, a6 := 7187035 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 11] }
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
end C99_d1

namespace C99_d2
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -93, a6 := 625 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 11, 11, 11, 11, 11] }
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
end C99_d2

namespace C99_d3
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -3, a6 := -5 }
def witness : MinimalityWitness := { primes := [3, 3, 3, 3, 3, 3, 11] }
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
end C99_d3

end VerifiedLcalc.EllipticCurve.AdditiveExpandedExamples
