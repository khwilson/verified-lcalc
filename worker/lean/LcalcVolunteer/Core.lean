module
public import VerifiedLcalc.EllipticCurve.DerivativeCore
public import VerifiedLcalc.EllipticCurve.WildRootCore
@[expose] public section
namespace LcalcVolunteer
open VerifiedLcalc VerifiedLcalc.EllipticCurve

/-- Untrusted search configuration. The server independently checks the result. -/
structure Request where
  equation : Artifacts.CurveEquation
  conductor : Nat
  bits : Nat := 53
  terms : Nat := 0
  steps : Nat := 1
  cutoff : Nat := 16
  deriving Repr

/-- A proposed witness, never a proof that the analytic rank is correct. -/
inductive Numerical where
  | central (value : CentralResult)
  | derivative (value : DerivativeResult)
  deriving Repr
structure Candidate where
  minimality : MinimalityWitness
  localData : WildData
  value : Numerical
  deriving Repr

def decode (line : String) : Option Request := do
  let fields := line.splitOn "\t"
  if fields.length != 10 then none else do
    let a1 ← fields[0]!.toInt?
    let a2 ← fields[1]!.toInt?
    let a3 ← fields[2]!.toInt?
    let a4 ← fields[3]!.toInt?
    let a6 ← fields[4]!.toInt?
    let N ← fields[5]!.toNat?
    let bits ← fields[6]!.toNat?
    let M ← fields[7]!.toNat?
    let steps ← fields[8]!.toNat?
    let cutoff ← fields[9]!.toNat?
    if N == 0 || N > 10000 || !(bits == 53 || bits == 80 || bits == 106) ||
        M > 128 || steps == 0 || steps > 16 || cutoff < 2 || cutoff > 64 then none
    else some ⟨⟨a1,a2,a3,a4,a6⟩,N,bits,M,steps,cutoff⟩

/-- Candidate search calls the existing proof-backed numerical routines.
Only emitted kernel-checked theorems are accepted by the service. -/
def compute (q : Request) : Option Candidate := do
  let e := q.equation
  let ps := (List.range (q.conductor+1)).filter isPrime
  let v ← minimalityWitness? e ps
  let d ← wildData? e
  let bad := ps.filter (fun (p : Nat) => discriminant e % (p : Int) == 0)
  let (level, sign) := wildConductorRootFromPrimes e d bad
  if level != q.conductor then none else do
    if sign == 1 then
      let mut result : Option CentralResult := none
      for bits in (if q.terms == 0 then [53,80,106] else [q.bits]) do
        for M in (if q.terms == 0 then [1,2,3,4,6,8,12,16,24,32,48,64,96,128] else [q.terms]) do
          if result.isNone then
            if let some r := evaluateCentral e q.conductor 1 M ⟨bits⟩ then
              if r.box.excludesZero then result := some r
      return ⟨v,d,.central (← result)⟩
    else if sign == -1 then
      let mut result : Option DerivativeResult := none
      let grids := if q.terms == 0 then
        [(1,8),(2,8),(1,16),(4,8),(2,16),(1,32),(8,8),(4,16),(2,32),(1,64),(8,16),(4,32),(2,64),(8,32),(4,64),(16,32)]
        else [(q.steps,q.cutoff)]
      for (steps,cutoff) in grids do
        for M in (if q.terms == 0 then [8,12,16,24,40,64,96,128] else [q.terms]) do
          if result.isNone then
            if let some r := evaluateDerivative e q.conductor M steps cutoff ⟨q.bits⟩ then
              if r.box.excludesZero then result := some r
      return ⟨v,d,.derivative (← result)⟩
    else none

-- All JSON integers are decimal strings, preserving precision in browsers.
def quote (s : String) : String := "\"" ++ s ++ "\""
def num [ToString α] (x : α) : String := quote (toString x)
def array (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
def object (xs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (xs.map fun (k,v) => quote k ++ ":" ++ v) ++ "}"
def rat (x : Rat) : String := quote (toString x.num ++ "/" ++ toString x.den)
def interval (x : Rat × Rat) : String := array [rat x.1,rat x.2]
def tate (w : TateWitness) : String := object [
  ("r",num w.r),("s",num w.s),("t",num w.t),("starT",num w.starT),
  ("cubicRoot",num w.cubicRoot),("quadraticRoot",num w.quadraticRoot),
  ("chain",array (w.chain.map num)),("kodaira",num w.kodaira)]
def optionalTate : Option TateWitness → String
  | none => "null"
  | some w => tate w

/-- Serialization is untrusted data plumbing; submitted JSON is independently
bound to the exact subject, parameters, and theorem by the validation service. -/
def encode (c : Candidate) : String := Id.run do
  let (e,N,bits,M,steps,cutoff,rank,cs,alpha,tail,box,extra) := match c.value with
    | .central r => (r.equation,r.conductor,r.policy.precisionBits,r.termLimit,0,0,0,
        r.coefficients,(r.alphaLo,r.alphaHi),r.tail,r.box,
        [("geometric_upper",rat r.geometricUpper)])
    | .derivative r => (r.equation,r.conductor,r.policy.precisionBits,r.termLimit,
        r.stepsPerUnit,r.cutoff,1,r.coefficients,(r.alphaLo,r.alphaHi),r.tail,r.box,
        [("finite",interval r.finite)])
  return object [
    ("schema",quote "lcalc.ec-rank.v1"),
    ("subject",object [("ainvs",array ([e.a1,e.a2,e.a3,e.a4,e.a6].map num)),("conductor",num N)]),
    ("parameters",object [("precision_bits",num bits),("terms",num M),
      ("steps_per_unit",num steps),("cutoff",num cutoff)]),
    ("rank",num rank),
    ("coefficients",array (cs.map num)),
    ("arithmetic",object [("minimality",array (c.minimality.primes.map num)),
      ("at_two",optionalTate c.localData.atTwo),("at_three",optionalTate c.localData.atThree)]),
    ("enclosure",object [("real",interval (box.reLo,box.reHi)),("imag",interval (box.imLo,box.imHi))]),
    ("evaluator",object ([("alpha",interval alpha),("tail",rat tail)] ++ extra))]

/-- Stable native/WASM entry point. A success is a proposed certificate only. -/
@[export lcalc_volunteer_compute]
def run (line : String) : String :=
  match decode line >>= compute with
  | some c => encode c
  | none => "{\"status\":\"inconclusive\"}"
end LcalcVolunteer
