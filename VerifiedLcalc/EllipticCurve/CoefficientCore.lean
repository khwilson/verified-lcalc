module

public import VerifiedLcalc.EllipticCurve.Arithmetic

@[expose] public section

namespace VerifiedLcalc.EllipticCurve

/-- Division-based valuation with a structural fuel bound. -/
def valuationFuel (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if 2 ≤ p ∧ 0 < n ∧ n % p = 0 then
      1 + valuationFuel p fuel (n / p)
    else 0

def primeExponent (p n : Nat) : Nat := valuationFuel p n n

structure ModelEulerFactor where
  prime : Nat
  trace : Int
  quadratic : Int
  deriving Repr, DecidableEq

/-- Equation-solution trace at every prime, including singular reduction.
Identifying a singular-model factor with the curve's Euler factor requires
minimality and the reduction-classification theorems; it is not automatic. -/
def modelFactor (e : (WeierstrassCurve ℤ)) (p : Nat) : ModelEulerFactor :=
  ⟨p, frobeniusTrace e p, if goodReduction e p then (p : Int) else 0⟩

def modelFactors (e : (WeierstrassCurve ℤ)) (limit : Nat) : List ModelEulerFactor :=
  ((List.range (limit + 1)).filter isPrime).map (modelFactor e)

def coefficientFromFactors (factors : List ModelEulerFactor) (n : Nat) : Int :=
  if n = 0 then 0 else
    (factors.map fun f =>
      let k := primeExponent f.prime n
      if k = 0 then 1 else localCoefficient f.trace f.quadratic k).prod

/-- a₁ through a_limit. Prime counts are computed once and shared by all rows. -/
def modelCoefficients (e : (WeierstrassCurve ℤ)) (limit : Nat) : List Int :=
  let factors := modelFactors e limit
  (List.range limit).map fun j => coefficientFromFactors factors (j + 1)

theorem modelFactor_correct (e : (WeierstrassCurve ℤ)) (p : Nat) :
    (modelFactor e p).prime = p ∧
    (modelFactor e p).trace = frobeniusTrace e p ∧
    (modelFactor e p).quadratic = if goodReduction e p then (p : Int) else 0 := by
  exact ⟨rfl, rfl, rfl⟩

theorem modelFactors_correct (e : (WeierstrassCurve ℤ)) (limit : Nat)
    (f : ModelEulerFactor) :
    f ∈ modelFactors e limit ↔
      ∃ p, p ≤ limit ∧ isPrime p = true ∧ f = modelFactor e p := by
  simp only [modelFactors, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨p, ⟨hp, hi⟩, hf⟩
    exact ⟨p, by omega, hi, hf.symm⟩
  · rintro ⟨p, hp, hi, hf⟩
    exact ⟨p, ⟨by omega, hi⟩, hf.symm⟩

theorem modelCoefficients_correct (e : (WeierstrassCurve ℤ)) (limit : Nat) :
    modelCoefficients e limit =
      (List.range limit).map (fun j => coefficientFromFactors (modelFactors e limit) (j + 1)) := rfl

end VerifiedLcalc.EllipticCurve
