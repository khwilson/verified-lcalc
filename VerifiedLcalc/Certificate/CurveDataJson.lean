module

public import VerifiedLcalc.Certification.CurveData
public import VerifiedLcalc.Certificate.Json
public import Mathlib.Data.Int.Sqrt

@[expose] public section

/-! Field-driven decoding of untrusted elliptic-curve data. Supported fields
are decoded exactly; mathematical claims are checked separately in the kernel.
Unknown metadata does not become a theorem. -/
namespace VerifiedLcalc.CurveDataJson
open Lean CertificateJson

/-- Accept canonical decimal strings and exact JSON integer literals. -/
def integer (j : Json) : Except String Int := do
  match j with
  | .str _ => decimal j
  | _ =>
    let n ← j.getInt?
    unless (toString n).length ≤ 512 do throw "Oversized integer"
    return n

def optional (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

/-- Optional aggregate fields use JSON null for `none`. -/
def optionalData (j : Json) (key : String) : Option Json :=
  (optional j key).bind fun value => if value == .null then none else some value

def ainvs (j : Json) : Except String (List Int) := do
  let a ← array j 5
  unless a.size == 5 do throw "Expected five Weierstrass coefficients"
  a.toList.mapM integer

/-- Use top-level or rank-witness `subject.ainvs`, rejecting conflicting models. -/
def equation (j : Json) : Except String (WeierstrassCurve ℤ) := do
  let nested := optional j "analytic_witness"
  let candidates := [optional j "ainvs",
    (optional j "subject").bind (optional · "ainvs"),
    nested.bind (optional · "ainvs"),
    (nested.bind (optional · "subject")).bind (optional · "ainvs")]
  let models ← (candidates.filterMap id).mapM ainvs
  let some a := models.head? | throw "Expected ainvs or subject.ainvs"
  unless models.all (· == a) do throw "Conflicting integral equations"
  let [a₁, a₂, a₃, a₄, a₆] := a | throw "Expected five coefficients"
  return ⟨a₁, a₂, a₃, a₄, a₆⟩

/-- Keep only a supported object's required fields; extra metadata is not a claim. -/
def project? (j : Json) (keys : List String) : Option Json := do
  let fields ← keys.mapM fun key => do
    return (key, ← optional j key)
  return Json.mkObj fields

def tateView? (j : Json) : Option Json :=
  if j == .null then some j else
    project? j ["r", "s", "t", "starT", "cubicRoot", "quadraticRoot", "chain", "kodaira"]

/-- An incomplete or unsupported rank observation stays metadata. A complete
supported witness is decoded strictly and must subsequently pass every proof check. -/
def rankView? (j : Json) : Option Json := do
  let rank ← ((j.getObjVal? "rank").bind integer).toOption
  guard (rank = 0 ∨ rank = 1)
  let subject ← project? (← optional j "subject") ["ainvs", "conductor"]
  let parameters ← project? (← optional j "parameters")
    ["precision_bits", "terms", "steps_per_unit", "cutoff"]
  let enclosure ← project? (← optional j "enclosure") ["real", "imag"]
  let evaluator ← project? (← optional j "evaluator")
    (if rank == 0 then ["alpha", "tail", "geometric_upper"] else ["alpha", "tail", "finite"])
  return Json.mkObj [
    ("schema", .str "lcalc.ec-rank.v1"), ("subject", subject), ("parameters", parameters),
    ("rank", .str (toString rank)), ("coefficients", ← optional j "coefficients"),
    ("arithmetic", Json.mkObj [("minimality", .arr #[]), ("at_two", .null), ("at_three", .null)]),
    ("enclosure", enclosure), ("evaluator", evaluator)]

def numericFields (j : Json) : Except String (Option EllipticWitness) := do
  match rankView? ((optional j "analytic_witness").getD j) with
  | none => return none
  | some view => return some (← CertificateJson.decode view)

/-- Decode optional minimality data independently of numerical payloads. -/
def minimalityField (j : Json) : Except String (Option EllipticCurve.MinimalityWitness) := do
  let source := (optional j "analytic_witness").getD j
  let legacy := (optional source "arithmetic").bind (optional · "minimality")
  let value := (optional j "minimality").orElse (fun _ => legacy)
  let some value := value | return none
  if value == .null then return none
  let values ← array ((optional value "primes").getD value) 256
  let primes ← values.toList.mapM fun value => do
    let p ← integer value
    unless 0 ≤ p do throw "Expected a nonnegative prime factor"
    return p.toNat
  return some ⟨primes⟩

/-- Preserve absence of local data; explicit null transcripts describe a
supplied `WildData` record and are checked for the curve in the usual way. -/
def localDataField (j : Json) : Except String (Option EllipticCurve.WildData) := do
  let source := (optional j "analytic_witness").getD j
  let legacy := optional source "arithmetic"
  let data := (optional j "local_data").orElse (fun _ => legacy)
  let some data := data | return none
  if data == .null then return none
  let two := optional data "at_two"
  let three := optional data "at_three"
  unless two.isSome || three.isSome do return none
  let decode (value : Option Json) : Except String (Option EllipticCurve.TateWitness) := do
    let value := value.getD .null
    let some view := tateView? value | throw "Incomplete Tate transcript"
    CertificateJson.tate view
  return some ⟨← decode two, ← decode three⟩

/-- Exact rational data: LMFDB numerator/positive-denominator pairs, fractions,
canonical integer strings, or exact JSON integers. No decimal approximation. -/
def rationalValue (j : Json) : Except String Rat := do
  match j with
  | .arr values =>
    unless values.size == 2 do throw "Expected a rational numerator/denominator pair"
    let n ← integer values[0]!
    let d ← integer values[1]!
    unless 0 < d do throw "Expected a positive rational denominator"
    return (n : Rat) / d
  | .str value =>
    if value.contains '/' then rational j else return (← integer j : Int)
  | _ => return (← integer j : Int)

def optionalValue (j : Json) (key : String) (decode : Json → Except String α) :
    Except String (Option α) := do
  match optionalData j key with
  | none => return none
  | some value => return some (← decode value)

def nonnegativeInteger (j : Json) : Except String Nat := do
  let n ← integer j
  unless 0 ≤ n do throw "Expected a nonnegative integer"
  return n.toNat

def bValues (j : Json) : Except String (Int × Int × Int × Int) := do
  let xs ← array j 4
  unless xs.size == 4 do throw "Expected b2,b4,b6,b8"
  return (← integer xs[0]!, ← integer xs[1]!, ← integer xs[2]!, ← integer xs[3]!)

def cValues (j : Json) : Except String (Int × Int) := do
  let xs ← array j 2
  unless xs.size == 2 do throw "Expected c4,c6"
  return (← integer xs[0]!, ← integer xs[1]!)

/-- Decode LMFDB weighted projective triples to exact rational affine coordinates. -/
def weightedCoordinates (j : Json) : Except String (List (Rat × Rat)) := do
  (← array j 4096).toList.mapM fun row => do
    let triple ← array row 3
    unless triple.size == 3 do throw "Expected a weighted affine point triple [a,b,c]"
    let a ← integer triple[0]!
    let b ← integer triple[1]!
    let c ← integer triple[2]!
    unless c != 0 do throw "Weighted affine point denominator must be nonzero"
    return ((a : Rat) / (c : Rat) ^ 2, (b : Rat) / (c : Rat) ^ 3)

/-- Decode whichever supported fields are present. Integer square-root
reconstruction supplies candidate y-coordinates for stored integral x-values;
the certifier subsequently proves every resulting curve equation. -/
def decode (j : Json) : Except String EllipticWitness := do
  let _ ← j.getObj?
  let equation ← equation j
  let mut primeCoefficients : Array (Nat × Int) := #[]
  if let some rows := optionalData j "ap" then
    for row in ← array rows 256 do
      let pair ← array row 2
      unless pair.size == 2 do throw "Expected a prime/coefficient pair"
      let p ← integer pair[0]!
      unless 2 ≤ p && p ≤ 10000 do throw "Prime index outside supported profile"
      primeCoefficients := primeCoefficients.push (p.toNat, ← integer pair[1]!)
  if let some rows := optionalData j "aplist" then
    let values ← (← array rows 256).toList.mapM integer
    let primes := ((List.range 10001).filter EllipticCurve.isPrime).take values.length
    unless primes.length == values.length do throw "Insufficient supported prime indices"
    primeCoefficients := primeCoefficients ++ (primes.zip values).toArray
  unless primeCoefficients.size ≤ 256 do throw "Too many prime coefficients"
  let mut integralCoordinates : Array (Int × Int) := #[]
  if let some rows := optionalData j "integral_points" then
    for row in ← array rows 4096 do
      let pair ← array row 2
      unless pair.size == 2 do throw "Expected an affine integer coordinate pair"
      integralCoordinates := integralCoordinates.push (← integer pair[0]!, ← integer pair[1]!)
  if let some rows := optionalData j "xcoord_integral_points" then
    for row in ← array rows 4096 do
      let x ← integer row
      let b := equation.a₁ * x + equation.a₃
      let c := x ^ 3 + equation.a₂ * x ^ 2 + equation.a₄ * x + equation.a₆
      let y := (-b + Int.sqrt (b ^ 2 + 4 * c)) / 2
      integralCoordinates := (integralCoordinates.push (x, y)).push (x, -y - b)
  unless integralCoordinates.size ≤ 8192 do throw "Too many integral coordinates"
  let generatorCoordinates ← optionalValue j "gens" weightedCoordinates
  let torsionGeneratorCoordinates ← optionalValue j "torsion_generators" weightedCoordinates
  let numeric ← numericFields j
  let base := numeric.getD { equation }
  let primeData := if (optionalData j "ap").isSome || (optionalData j "aplist").isSome
    then some primeCoefficients.toList else none
  let pointData := if (optionalData j "integral_points").isSome || (optionalData j "xcoord_integral_points").isSome
    then some integralCoordinates.toList else none
  let minimality ← minimalityField j
  let localData ← localDataField j
  let indices (key : String) : Except String (Option (List Nat)) := do
    let some value := optionalData j key | return none
    let rows ← array value 8192
    return some (← rows.toList.mapM fun row => do
      let i ← integer row
      unless 0 ≤ i && i < 8192 do throw "Point index outside supported profile"
      return i.toNat)
  let infiniteOrderPoints ← indices "infinite_order_points"
  let independentPoints ← indices "independent_points"
  let bInvariants ← optionalValue j "binvs" bValues
  let cInvariants ← optionalValue j "cinvs" cValues
  let discriminant ← optionalValue j "discriminant" integer
  let jInvariant ← optionalValue j "jinv" rationalValue
  let discriminantSign ← optionalValue j "signD" integer
  let minimalDiscriminantAbs ← optionalValue j "absD" nonnegativeInteger
  let conductor ← optionalValue j "conductor" nonnegativeInteger
  let rootNumber ← optionalValue j "global_root_number" integer
  let dirichletCoefficients ← optionalValue j "anlist" fun value => do
    let xs ← (← array value 256).toList.mapM integer
    match xs with
    | [] => return []
    | a₀ :: rest =>
      unless a₀ == 0 do throw "LMFDB anlist must start with a_0 = 0"
      return rest
  let badPrimes ← optionalValue j "bad_primes" fun value => do
    (← array value 256).toList.mapM nonnegativeInteger
  let numBadPrimes ← optionalValue j "num_bad_primes" nonnegativeInteger
  return { base with
    equation
    bInvariants
    cInvariants
    discriminant
    jInvariant
    discriminantSign
    minimalDiscriminantAbs
    conductor
    rootNumber
    dirichletCoefficients
    badPrimes
    numBadPrimes
    primeCoefficients := primeData
    integralCoordinates := pointData
    generatorCoordinates
    torsionGeneratorCoordinates
    infiniteOrderPoints
    independentPoints
    minimality
    localData }

/-- Bounded local parsing, with optional metadata and no analytic witness search. -/
def parse (text : String) : Except String EllipticWitness := do
  unless text.utf8ByteSize ≤ 2 * 1024 * 1024 do throw "Witness exceeds 2 MiB"
  decode (← Json.parse text)

end VerifiedLcalc.CurveDataJson
