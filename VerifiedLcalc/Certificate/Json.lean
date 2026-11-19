module

public import VerifiedLcalc.Certificate.EllipticWitness
public import Lean.Data.Json

@[expose] public section

/-! Exact data decoding only. No witness search or mathematical certification.
JSON numbers are decimal/rational strings, preserving all input precision. -/
namespace VerifiedLcalc.CertificateJson
open Lean EllipticCurve

def keys (j : Json) (expected : List String) : Except String Unit := do
  let obj ← j.getObj?
  unless obj.size == expected.length && expected.all (obj.contains ·) do
    throw s!"Expected exactly the fields {expected}"

def field (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

def decimal (j : Json) (signed := true) : Except String Int := do
  let s ← j.getStr?
  unless s.length ≤ 512 do throw "Oversized integer"
  let some n := s.toInt? | throw "Expected decimal integer string"
  unless toString n == s && (signed || n ≥ 0) do throw "Expected canonical decimal integer string"
  return n

def natural (j : Json) : Except String Nat := do
  return (← decimal j false).toNat

def rational (j : Json) : Except String Rat := do
  let s ← j.getStr?
  unless s.length ≤ 1024 do throw "Oversized rational"
  let [n,d] := s.splitOn "/" | throw "Expected numerator/denominator"
  let n ← decimal (.str n)
  let d ← natural (.str d)
  if d == 0 then throw "Zero denominator"
  return (n : Rat) / d

def array (j : Json) (limit : Nat) : Except String (Array Json) := do
  let xs ← j.getArr?
  unless xs.size ≤ limit do throw "Oversized array"
  return xs

def interval (j : Json) : Except String (Rat × Rat) := do
  let xs ← array j 2
  unless xs.size == 2 do throw "Expected two interval endpoints"
  return (← rational xs[0]!, ← rational xs[1]!)

def tate (j : Json) : Except String (Option TateWitness) := do
  if j == .null then return none
  keys j ["r", "s", "t", "starT", "cubicRoot", "quadraticRoot", "chain", "kodaira"]
  let r ← field j "r" >>= decimal
  let s ← field j "s" >>= decimal
  let t ← field j "t" >>= decimal
  let starT ← field j "starT" >>= decimal
  let cubicRoot ← field j "cubicRoot" >>= decimal
  let quadraticRoot ← field j "quadraticRoot" >>= decimal
  let kodaira ← field j "kodaira" >>= decimal
  let chain ← (← field j "chain" >>= (array · 64)).toList.mapM (decimal ·)
  return some { r, s, t, starT, cubicRoot, quadraticRoot, kodaira, chain }

/-- Strict, bounded decoding of the existing portable witness format. Success
is data only; every mathematical condition is subsequently kernel checked. -/
def decode (j : Json) : Except String EllipticWitness := do
  keys j ["schema", "subject", "parameters", "rank", "coefficients", "arithmetic", "enclosure", "evaluator"]
  unless (← field j "schema" >>= Json.getStr?) == "lcalc.ec-rank.v1" do
    throw "Unsupported witness schema"
  let rank ← field j "rank" >>= Json.getStr?
  unless rank == "0" || rank == "1" do throw "Only rank zero/one witnesses are supported"
  let subject ← field j "subject"
  keys subject ["ainvs", "conductor"]
  let a ← field subject "ainvs" >>= (array · 5)
  unless a.size == 5 do throw "Expected five Weierstrass coefficients"
  let equation : (WeierstrassCurve ℤ) := ⟨← decimal a[0]!, ← decimal a[1]!, ← decimal a[2]!, ← decimal a[3]!, ← decimal a[4]!⟩
  let conductor ← field subject "conductor" >>= natural
  unless 0 < conductor && conductor ≤ 10000 do throw "Conductor outside supported profile"
  let p ← field j "parameters"
  keys p ["precision_bits", "terms", "steps_per_unit", "cutoff"]
  let bits ← field p "precision_bits" >>= natural
  let termLimit ← field p "terms" >>= natural
  let steps ← field p "steps_per_unit" >>= natural
  let cutoff ← field p "cutoff" >>= natural
  unless (bits == 53 || bits == 80 || bits == 106) && 0 < termLimit && termLimit ≤ 128 do
    throw "Unsupported numerical settings"
  let coefficients ← (← field j "coefficients" >>= (array · 128)).toList.mapM (decimal ·)
  unless coefficients.length == termLimit do throw "Coefficient count differs from terms"
  let a ← field j "arithmetic"
  keys a ["minimality", "at_two", "at_three"]
  let primes ← (← field a "minimality" >>= (array · 256)).toList.mapM natural
  let minimality : MinimalityWitness := ⟨primes⟩
  let atTwo ← field a "at_two" >>= tate
  let atThree ← field a "at_three" >>= tate
  let localData : WildData := ⟨atTwo, atThree⟩
  let enclosure ← field j "enclosure"
  keys enclosure ["real", "imag"]
  let re ← field enclosure "real" >>= interval
  let im ← field enclosure "imag" >>= interval
  let box : Box := ⟨re.1,re.2,im.1,im.2⟩
  let e ← field j "evaluator"
  keys e (if rank == "0" then ["alpha", "tail", "geometric_upper"] else ["alpha", "tail", "finite"])
  let alpha ← field e "alpha" >>= interval
  let tail ← field e "tail" >>= rational
  if rank == "0" then
    unless steps == 0 && cutoff == 0 do throw "Rank zero has no derivative grid"
    let geometricUpper ← field e "geometric_upper" >>= rational
    return .central { equation, conductor, rootNumber := 1, policy := ⟨bits⟩, termLimit, coefficients, alphaLo := alpha.1, alphaHi := alpha.2, geometricUpper, tail, box } minimality localData
  else
    unless 0 < steps && steps ≤ 16 && 2 ≤ cutoff && cutoff ≤ 64 do throw "Unsupported derivative grid"
    let finite ← field e "finite" >>= interval
    return .derivative { equation, conductor, policy := ⟨bits⟩, termLimit, stepsPerUnit := steps, cutoff, coefficients, alphaLo := alpha.1, alphaHi := alpha.2, finite, tail, box } minimality localData

/-- Parse a local witness; no floating-point data or executable Lean source. -/
def parse (text : String) : Except String EllipticWitness := do
  unless text.utf8ByteSize ≤ 2 * 1024 * 1024 do throw "Witness exceeds 2 MiB"
  decode (← Json.parse text)

end VerifiedLcalc.CertificateJson
