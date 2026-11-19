module
public import LcalcVolunteer.Source
@[expose] public section
namespace LcalcVolunteer
open VerifiedLcalc VerifiedLcalc.EllipticCurve

-- Untrusted transport decoder. The kernel checks the emitted proof and independent
-- equalities binding every decoded value to the submitted JSON. No search here.
def witnessRat (s : String) : Option Rat := do
  let [n,d] := s.splitOn "/" | none
  let n ← n.toInt?
  let d ← d.toNat?
  if d == 0 then none else some ((n : Rat) / d)

def witnessList (s : String) (parse : String → Option α) : Option (List α) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM parse

def witnessTate (s : String) : Option (Option TateWitness) := do
  if s == "none" then return none
  let [head,chain] := s.splitOn ";" | none
  let [r,s,t,starT,cubicRoot,quadraticRoot,kodaira] ← witnessList head String.toInt? | none
  let chain ← witnessList chain String.toInt?
  return some { r, s, t, starT, cubicRoot, quadraticRoot, kodaira, chain }

def decodeWitness (line : String) : Option Candidate := do
  let f := line.splitOn "\t"
  if f.length != 25 then none else do
    let a1 ← f[1]!.toInt?
    let a2 ← f[2]!.toInt?
    let a3 ← f[3]!.toInt?
    let a4 ← f[4]!.toInt?
    let a6 ← f[5]!.toInt?
    let equation : Artifacts.CurveEquation := ⟨a1,a2,a3,a4,a6⟩
    let conductor ← f[6]!.toNat?
    let precisionBits ← f[7]!.toNat?
    let termLimit ← f[8]!.toNat?
    let stepsPerUnit ← f[9]!.toNat?
    let cutoff ← f[10]!.toNat?
    let coefficients ← witnessList f[11]! String.toInt?
    let primes ← witnessList f[12]! String.toNat?
    let atTwo ← witnessTate f[13]!
    let atThree ← witnessTate f[14]!
    let alphaLo ← witnessRat f[15]!
    let alphaHi ← witnessRat f[16]!
    let tail ← witnessRat f[17]!
    let reLo ← witnessRat f[18]!
    let reHi ← witnessRat f[19]!
    let imLo ← witnessRat f[20]!
    let imHi ← witnessRat f[21]!
    let box : Box := ⟨reLo,reHi,imLo,imHi⟩
    let value ← if f[0]! == "0" then do
      let geometricUpper ← witnessRat f[22]!
      pure (Numerical.central { equation, conductor, rootNumber := 1, policy := ⟨precisionBits⟩, termLimit, coefficients, alphaLo, alphaHi, geometricUpper, tail, box })
      else if f[0]! == "1" then do
        let lo ← witnessRat f[23]!
        let hi ← witnessRat f[24]!
        pure (Numerical.derivative { equation, conductor, policy := ⟨precisionBits⟩, termLimit, stepsPerUnit, cutoff, coefficients, alphaLo, alphaHi, finite := (lo,hi), tail, box })
      else none
    return ⟨⟨primes⟩,⟨atTwo,atThree⟩,value⟩
end LcalcVolunteer
