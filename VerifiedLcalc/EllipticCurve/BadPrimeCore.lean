module

public import VerifiedLcalc.EllipticCurve.ReductionCore

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Evaluation of the tangent quadratic defining split multiplicative reduction. -/
def nodeValue (e : (WeierstrassCurve ℤ)) (x : Int) : Int :=
  modelC4 e * x ^ 2 + e.a₁ * modelC4 e * x -
    (54 * e.b₆ - 3 * e.b₂ * e.b₄ + e.a₂ * modelC4 e)

/-- Linear search for a root, rather than quadratic enumeration of equation points. -/
def hasNodeRoot (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  (List.range p).any (fun x => decide (nodeValue e x % (p : Int) = 0))

/-- Trace at a bad prime of the supplied equation. Correctness is proved for
prime p and vanishing discriminant in BadPrime.lean. -/
def singularTrace (e : (WeierstrassCurve ℤ)) (p : Nat) : Int :=
  if modelC4 e % (p : Int) = 0 then 0 else if hasNodeRoot e p then 1 else -1

end VerifiedLcalc.EllipticCurve
