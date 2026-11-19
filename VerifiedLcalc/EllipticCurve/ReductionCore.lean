module

public import VerifiedLcalc.EllipticCurve.CoefficientCore

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Invariant c4 of the supplied integral equation. -/
def modelC4 (e : Artifacts.CurveEquation) : Int := (b2 e) ^ 2 - 24 * b4 e

/-- Invariant c6 of the supplied integral equation. -/
def modelC6 (e : Artifacts.CurveEquation) : Int :=
  -(b2 e) ^ 3 + 36 * b2 e * b4 e - 216 * b6 e

/-- Classification of the supplied equation's reduction. Minimality is checked
separately before this classification is attributed to the elliptic curve. -/
inductive ModelReduction where
  | good | multiplicative | additive
  deriving Repr, DecidableEq

def modelReduction (e : Artifacts.CurveEquation) (p : Nat) : ModelReduction :=
  if discriminant e % (p : Int) != 0 then .good
  else if modelC4 e % (p : Int) != 0 then .multiplicative
  else .additive

/-- A sufficient minimality test at a specified prime, including additive primes.
False means that the criterion is inconclusive, not that the model is nonminimal. -/
def discriminantMinimalAt (e : Artifacts.CurveEquation) (p : Nat) : Bool :=
  decide (discriminant e % (p : Int) ^ 12 ≠ 0)

/-- A second sufficient criterion, for residue characteristic two with c4
valuation exactly six. The invariant gap is proved in TwoAdicMinimality. -/
def twoAdicC4MinimalAt (e : Artifacts.CurveEquation) (p : Nat) : Bool :=
  decide (p = 2 ∧ modelC4 e % 64 = 0 ∧ modelC4 e % 128 ≠ 0)

/-- The two further standard sufficient minimality criteria. -/
def invariantMinimalAt (e : Artifacts.CurveEquation) (p : Nat) : Bool :=
  decide (modelC4 e % (p : Int) ^ 4 ≠ 0 ∨ modelC6 e % (p : Int) ^ 6 ≠ 0)

def modelMinimalAt (e : Artifacts.CurveEquation) (p : Nat) : Bool :=
  discriminantMinimalAt e p || twoAdicC4MinimalAt e p || invariantMinimalAt e p

/-- A finite, explicit factorization witness. Primes outside this list are good.
Both the factorization and the minimality checks are rechecked in the kernel. -/
structure MinimalityWitness where
  primes : List Nat
  deriving Repr, DecidableEq

/-- A prime factorization with repetition, plus minimality checks at its primes.
The producer may supply any list; the kernel validates every assertion. -/
def MinimalityWitness.Valid (w : MinimalityWitness) (e : Artifacts.CurveEquation) : Prop :=
  w.primes.all (fun p => isPrime p && modelMinimalAt e p) = true ∧
  w.primes.prod = (discriminant e).natAbs

instance (w : MinimalityWitness) (e : Artifacts.CurveEquation) : Decidable (w.Valid e) := by
  unfold MinimalityWitness.Valid
  infer_instance

/-- Search using candidate primes. Incomplete candidate lists simply fail the
exact factorization check. No conductor assertion is trusted here. -/
def minimalityWitness? (e : Artifacts.CurveEquation) (candidates : List Nat) :
    Option MinimalityWitness :=
  let w : MinimalityWitness := ⟨candidates.flatMap (fun p =>
    List.replicate (primeExponent p (discriminant e).natAbs) p)⟩
  if w.Valid e then some w else none

/-- The untrusted factorization search only returns validated witnesses. -/
theorem minimalityWitness?_sound (e : Artifacts.CurveEquation) (candidates : List Nat)
    (w : MinimalityWitness) (h : minimalityWitness? e candidates = some w) : w.Valid e := by
  unfold minimalityWitness? at h
  dsimp only at h
  split at h
  · next hw => cases Option.some.inj h; exact hw
  · contradiction

end VerifiedLcalc.EllipticCurve
