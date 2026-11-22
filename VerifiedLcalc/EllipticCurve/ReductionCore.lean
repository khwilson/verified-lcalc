module

public import VerifiedLcalc.EllipticCurve.CoefficientCore
public import VerifiedLcalc.Certificates.Transcripts

/-! # Reduction classification from checked transcripts -/

@[expose] public section
namespace VerifiedLcalc.EllipticCurve

/-- Classification of the supplied equation's reduction. Minimality is checked
separately before this classification is attributed to the elliptic curve. -/
inductive ModelReduction where
  | good | multiplicative | additive
  deriving Repr, DecidableEq

/-- Classify the supplied integral model by its reduction discriminant and c4. -/
def modelReduction (e : (WeierstrassCurve ℤ)) (p : Nat) : ModelReduction :=
  if e.Δ % (p : Int) != 0 then .good
  else if e.c₄ % (p : Int) != 0 then .multiplicative
  else .additive

/-- A sufficient minimality test at a specified prime, including additive primes.
False means that the criterion is inconclusive, not that the model is nonminimal. -/
def discriminantMinimalAt (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  decide (e.Δ % (p : Int) ^ 12 ≠ 0)

/-- A second sufficient criterion, for residue characteristic two with c4
valuation exactly six. The invariant gap is proved in TwoAdicMinimality. -/
def twoAdicC4MinimalAt (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  decide (p = 2 ∧ e.c₄ % 64 = 0 ∧ e.c₄ % 128 ≠ 0)

/-- The two further standard sufficient minimality criteria. -/
def invariantMinimalAt (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  decide (e.c₄ % (p : Int) ^ 4 ≠ 0 ∨ e.c₆ % (p : Int) ^ 6 ≠ 0)

/-- Boolean check of the model minimality conditions at p. -/
def modelMinimalAt (e : (WeierstrassCurve ℤ)) (p : Nat) : Bool :=
  discriminantMinimalAt e p || twoAdicC4MinimalAt e p || invariantMinimalAt e p

/-- A prime factorization with repetition, plus minimality checks at its primes.
The producer may supply any list; the kernel validates every assertion. -/
def MinimalityWitness.Valid (w : MinimalityWitness) (e : (WeierstrassCurve ℤ)) : Prop :=
  w.primes.all (fun p => isPrime p && modelMinimalAt e p) = true ∧
  w.primes.prod = (e.Δ).natAbs

instance (w : MinimalityWitness) (e : (WeierstrassCurve ℤ)) : Decidable (w.Valid e) := by
  unfold MinimalityWitness.Valid
  infer_instance

/-- Search using candidate primes. Incomplete candidate lists simply fail the
exact factorization check. No conductor assertion is trusted here. -/
def minimalityWitness? (e : (WeierstrassCurve ℤ)) (candidates : List Nat) :
    Option MinimalityWitness :=
  let w : MinimalityWitness := ⟨candidates.flatMap (fun p =>
    List.replicate (padicValNat p (e.Δ).natAbs) p)⟩
  if w.Valid e then some w else none

/-- The untrusted factorization search only returns validated witnesses. -/
theorem minimalityWitness?_sound (e : (WeierstrassCurve ℤ)) (candidates : List Nat)
    (w : MinimalityWitness) (h : minimalityWitness? e candidates = some w) : w.Valid e := by
  unfold minimalityWitness? at h
  dsimp only at h
  split at h
  · next hw => cases Option.some.inj h; exact hw
  · contradiction

end VerifiedLcalc.EllipticCurve
