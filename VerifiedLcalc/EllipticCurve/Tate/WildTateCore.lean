module

public import VerifiedLcalc.EllipticCurve.Tate.TameCore

@[expose] public section
namespace VerifiedLcalc.EllipticCurve
open Artifacts

/-- Integral change x=x'+r, y=y'+s*x'+t (u=1). -/
def translateIntegral (e : (WeierstrassCurve ℤ)) (r s t : Int) : (WeierstrassCurve ℤ) :=
  ⟨e.a₁ + 2*s, e.a₂ - s*e.a₁ + 3*r - s^2,
    e.a₃ + r*e.a₁ + 2*t,
    e.a₄ - s*e.a₃ + 2*r*e.a₂ - (t+r*s)*e.a₁ + 3*r^2 - 2*s*t,
    e.a₆ + r*e.a₄ + r^2*e.a₂ + r^3 - t*e.a₃ - t^2 - r*t*e.a₁⟩

/-- Tate's exact integral divisibility conditions. -/
def TateDiv (p : Nat) (k : Nat) (a : Int) : Prop := a % (p : Int)^k = 0
  deriving Decidable

def TateWeights (e : (WeierstrassCurve ℤ)) (p n1 n2 n3 n4 n6 : Nat) : Prop :=
  TateDiv p n1 e.a₁ ∧ TateDiv p n2 e.a₂ ∧ TateDiv p n3 e.a₃ ∧
    TateDiv p n4 e.a₄ ∧ TateDiv p n6 e.a₆
  deriving Decidable

def cubicRepeated (p : Nat) (a b c x : Int) : Prop :=
  (x^3+a*x^2+b*x+c) % (p : Int) = 0 ∧
    (3*x^2+2*a*x+b) % (p : Int) = 0
  deriving Decidable

def quadraticRepeated (p : Nat) (a b c x : Int) : Prop :=
  (a*x^2+b*x+c) % (p : Int) = 0 ∧ (2*a*x+b) % (p : Int) = 0
  deriving Decidable

/-- Separability tests in the finite residue field. In degrees two and three,
a repeated root of the polynomials occurring in Tate's algorithm lies in Fp. -/
def cubicSeparable (p : Nat) (a b c : Int) : Prop :=
  ∀ x ∈ List.range p, ¬ cubicRepeated p a b c x
  deriving Decidable

def quadraticSeparable (p : Nat) (a b c : Int) : Prop :=
  ∀ x ∈ List.range p, ¬ quadraticRepeated p a b c x
  deriving Decidable

/-- The I_n* chain: an empty list ends at a separable quadratic; each listed
root is checked before its integral translation and the next blow-up test.
No fuel bound or proposed Kodaira label is trusted by this predicate. -/
def StarChain (p : Nat) (e : (WeierstrassCurve ℤ)) (oddStage : Bool) (k : Nat) : List Int → Prop
  | [] =>
    if oddStage then
      TateDiv p k e.a₃ ∧ TateDiv p (2*k) e.a₆ ∧
        quadraticSeparable p 1 (e.a₃ / (p : Int)^k) (-(e.a₆ / (p : Int)^(2*k)))
    else
      TateDiv p (k+1) e.a₄ ∧ TateDiv p (2*k+1) e.a₆ ∧
        quadraticSeparable p (e.a₂ / p) (e.a₄ / (p : Int)^(k+1))
          (e.a₆ / (p : Int)^(2*k+1))
  | x :: xs =>
    0 ≤ x ∧ x < p ∧
    if oddStage then
      TateDiv p k e.a₃ ∧ TateDiv p (2*k) e.a₆ ∧
        quadraticRepeated p 1 (e.a₃ / (p : Int)^k) (-(e.a₆ / (p : Int)^(2*k))) x ∧
        StarChain p (translateIntegral e 0 0 (x*(p : Int)^k)) false k xs
    else
      TateDiv p (k+1) e.a₄ ∧ TateDiv p (2*k+1) e.a₆ ∧
        quadraticRepeated p (e.a₂ / p) (e.a₄ / (p : Int)^(k+1))
          (e.a₆ / (p : Int)^(2*k+1)) x ∧
        StarChain p (translateIntegral e (x*(p : Int)^k) 0 0) true (k+1) xs

def decStarChain (p : Nat) (e : (WeierstrassCurve ℤ)) (oddStage : Bool) (k : Nat)
    (xs : List Int) : Decidable (StarChain p e oddStage k xs) :=
  match xs with
  | [] => by unfold StarChain; split <;> infer_instance
  | x :: xs => by
    letI := decStarChain p (translateIntegral e 0 0 (x*(p : Int)^k)) false k xs
    letI := decStarChain p (translateIntegral e (x*(p : Int)^k) 0 0) true (k+1) xs
    unfold StarChain
    split <;> infer_instance

instance (p : Nat) (e : (WeierstrassCurve ℤ)) (oddStage : Bool) (k : Nat) (xs : List Int) :
    Decidable (StarChain p e oddStage k xs) := decStarChain p e oddStage k xs

/-- A finite Tate reduction transcript. Codes: II=2, III=3, IV=4,
I0*=-1, IV*=-4, III*=-3, II*=-2, I_n*=-(4+n). -/
structure TateWitness where
  r : Int
  s : Int
  t : Int
  starT : Int := 0
  cubicRoot : Int := 0
  quadraticRoot : Int := 0
  chain : List Int := []
  kodaira : Int
  deriving Repr, DecidableEq

/-- Number of geometric components minus one, in Ogg's conductor formula. -/
def TateWitness.offset (w : TateWitness) : Nat :=
  match w.kodaira with
  | 2 => 0 | 3 => 1 | 4 => 2 | -1 => 4
  | -4 => 6 | -3 => 7 | -2 => 8 | _ => 5+w.chain.length

/-- Declarative Tate path conditions. These are integer polynomial congruences,
not a test against a database conductor or the producer's own return value. -/
def TateWitness.Path (w : TateWitness) (e : (WeierstrassCurve ℤ)) (p : Nat) : Prop :=
  let a := translateIntegral e w.r w.s w.t
  TateWeights a p 1 1 1 1 1 ∧
  if w.kodaira = 2 then ¬ TateDiv p 2 a.a₆
  else TateDiv p 2 a.a₆ ∧
    if w.kodaira = 3 then ¬ TateDiv p 3 (a.b₈)
    else TateDiv p 3 (a.b₈) ∧
      if w.kodaira = 4 then ¬ TateDiv p 3 (a.b₆)
      else TateDiv p 3 (a.b₆) ∧
        let b := translateIntegral a 0 0 (w.starT*p)
        TateWeights b p 1 1 2 2 3 ∧
        let aa := b.a₂ / p
        let bb := b.a₄ / (p : Int)^2
        let cc := b.a₆ / (p : Int)^3
        if w.kodaira = -1 then cubicSeparable p aa bb cc
        else cubicRepeated p aa bb cc w.cubicRoot ∧
          let c := translateIntegral b (w.cubicRoot*p) 0 0
          if w.kodaira < -4 then
            (aa+3*w.cubicRoot) % (p : Int) ≠ 0 ∧
            w.kodaira = -(5 + (w.chain.length : Int)) ∧
            StarChain p c true 2 w.chain
          else TateWeights c p 1 2 2 3 4 ∧
            if w.kodaira = -4 then
              quadraticSeparable p 1 (c.a₃/(p : Int)^2) (-(c.a₆/(p : Int)^4))
            else quadraticRepeated p 1 (c.a₃/(p : Int)^2) (-(c.a₆/(p : Int)^4)) w.quadraticRoot ∧
              let d := translateIntegral c 0 0 (w.quadraticRoot*(p : Int)^2)
              TateWeights d p 1 2 3 3 5 ∧
              if w.kodaira = -3 then ¬ TateDiv p 4 d.a₄
              else w.kodaira = -2 ∧ TateDiv p 4 d.a₄ ∧ ¬ TateDiv p 6 d.a₆
  deriving Decidable

/-- A checked classification of a nonsingular additive minimal input at 2 or 3.
Minimality itself is supplied separately by the existing arithmetic proofs. -/
def TateWitness.Valid (w : TateWitness) (e : (WeierstrassCurve ℤ)) (p : Nat) : Prop :=
  (p = 2 ∨ p = 3) ∧ e.Δ ≠ 0 ∧ modelReduction e p = .additive ∧
    w.Path e p ∧ w.offset < padicValNat p (e.Δ).natAbs
  deriving Decidable

/-- Candidate search is allowed to stop; every returned chain is checked again
by the declarative predicate above before it can enter a certificate. -/
def starChainCandidate (p : Nat) (e : (WeierstrassCurve ℤ)) (oddStage : Bool) (k : Nat) :
    Nat → Option (List Int)
  | 0 => none
  | fuel+1 => do
    let a := if oddStage then 1 else e.a₂ / p
    let b := if oddStage then e.a₃/(p : Int)^k else e.a₄/(p : Int)^(k+1)
    let c := if oddStage then -(e.a₆/(p : Int)^(2*k)) else e.a₆/(p : Int)^(2*k+1)
    match (List.range p).find? (fun (x : Nat) => decide (quadraticRepeated p a b c x)) with
    | none => return []
    | some x =>
      let e' := if oddStage then translateIntegral e 0 0 (x*(p : Int)^k)
        else translateIntegral e (x*(p : Int)^k) 0 0
      let xs ← starChainCandidate p e' (!oddStage) (if oddStage then k else k+1) fuel
      return (x : Int) :: xs

def tateCandidate (e : (WeierstrassCurve ℤ)) (p : Nat) : Option TateWitness := do
  let triples := (List.range p).flatMap fun (r : Nat) => (List.range p).flatMap fun (s : Nat) =>
    (List.range p).map fun (t : Nat) => ((r : Int), (s : Int), (t : Int))
  let (r,s,t) ← triples.find? fun (r,s,t) => decide (TateWeights (translateIntegral e r s t) p 1 1 1 1 1)
  let a := translateIntegral e r s t
  let base : TateWitness := ⟨r,s,t,0,0,0,[],2⟩
  if ¬ TateDiv p 2 a.a₆ then return base
  if ¬ TateDiv p 3 (a.b₈) then return {base with kodaira := 3}
  if ¬ TateDiv p 3 (a.b₆) then return {base with kodaira := 4}
  let st ← (List.range p).find? fun (st : Nat) =>
    decide (TateWeights (translateIntegral a 0 0 (st*(p : Int))) p 1 1 2 2 3)
  let b := translateIntegral a 0 0 (st*(p : Int))
  let aa := b.a₂ / p
  let bb := b.a₄/(p : Int)^2
  let cc := b.a₆/(p : Int)^3
  let base := {base with starT := st}
  match (List.range p).find? (fun (x : Nat) => decide (cubicRepeated p aa bb cc x)) with
  | none => return {base with kodaira := -1}
  | some x =>
    let base := {base with cubicRoot := x}
    let c := translateIntegral b (x*(p : Int)) 0 0
    if (aa+3*(x : Int)) % (p : Int) ≠ 0 then
      let chain ← starChainCandidate p c true 2 (padicValNat p (e.Δ).natAbs + 1)
      return {base with chain := chain, kodaira := -(5+(chain.length : Int))}
    match (List.range p).find? (fun (x : Nat) =>
        decide (quadraticRepeated p 1 (c.a₃/(p : Int)^2) (-(c.a₆/(p : Int)^4)) x)) with
    | none => return {base with kodaira := -4}
    | some y =>
      let d := translateIntegral c 0 0 (y*(p : Int)^2)
      return {base with quadraticRoot := y, kodaira := if ¬ TateDiv p 4 d.a₄ then -3 else -2}

def tateWitness? (e : (WeierstrassCurve ℤ)) (p : Nat) : Option TateWitness := do
  if p != 2 && p != 3 then none else do
    let w ← tateCandidate e p
    if w.Valid e p then some w else none

/-- Correctness of the public search: success supplies a full checked Tate
transcript, independent of candidate completeness or its resource bound. -/
theorem tateWitness?_sound (e : (WeierstrassCurve ℤ)) (p : Nat) (w : TateWitness)
    (h : tateWitness? e p = some w) : w.Valid e p := by
  unfold tateWitness? at h
  split at h
  · simp at h
  · cases hc : tateCandidate e p with
    | none => simp [hc] at h
    | some v =>
      by_cases hv : v.Valid e p
      · simp [hc, hv] at h
        cases h
        exact hv
      · simp [hc, hv] at h

end VerifiedLcalc.EllipticCurve
