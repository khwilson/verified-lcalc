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
  let arithmetic ← optional j "arithmetic"
  let minimality ← optional arithmetic "minimality"
  let atTwo ← tateView? (← optional arithmetic "at_two")
  let atThree ← tateView? (← optional arithmetic "at_three")
  let enclosure ← project? (← optional j "enclosure") ["real", "imag"]
  let evaluator ← project? (← optional j "evaluator")
    (if rank == 0 then ["alpha", "tail", "geometric_upper"] else ["alpha", "tail", "finite"])
  return Json.mkObj [
    ("schema", .str "lcalc.ec-rank.v1"), ("subject", subject), ("parameters", parameters),
    ("rank", .str (toString rank)), ("coefficients", ← optional j "coefficients"),
    ("arithmetic", Json.mkObj [("minimality", minimality), ("at_two", atTwo), ("at_three", atThree)]),
    ("enclosure", enclosure), ("evaluator", evaluator)]

def analyticWitness (j : Json) : Except String (Option EllipticWitness) := do
  match rankView? ((optional j "analytic_witness").getD j) with
  | none => return none
  | some view => return some (← CertificateJson.decode view)

/-- Decode whichever supported fields are present. Integer square-root
reconstruction supplies candidate y-coordinates for stored integral x-values;
the certifier subsequently proves every resulting curve equation. -/
def decode (j : Json) : Except String CurveDataWitness := do
  let _ ← j.getObj?
  let equation ← equation j
  let mut primeCoefficients : Array (Nat × Int) := #[]
  if let some rows := optional j "ap" then
    for row in ← array rows 256 do
      let pair ← array row 2
      unless pair.size == 2 do throw "Expected a prime/coefficient pair"
      let p ← integer pair[0]!
      unless 2 ≤ p && p ≤ 10000 do throw "Prime index outside supported profile"
      primeCoefficients := primeCoefficients.push (p.toNat, ← integer pair[1]!)
  if let some rows := optional j "aplist" then
    let values ← (← array rows 256).toList.mapM integer
    let primes := ((List.range 10001).filter EllipticCurve.isPrime).take values.length
    unless primes.length == values.length do throw "Insufficient supported prime indices"
    primeCoefficients := primeCoefficients ++ (primes.zip values).toArray
  unless primeCoefficients.size ≤ 256 do throw "Too many prime coefficients"
  let mut integralCoordinates : Array (Int × Int) := #[]
  if let some rows := optional j "integral_points" then
    for row in ← array rows 4096 do
      let pair ← array row 2
      unless pair.size == 2 do throw "Expected an affine integer coordinate pair"
      integralCoordinates := integralCoordinates.push (← integer pair[0]!, ← integer pair[1]!)
  if let some rows := optional j "xcoord_integral_points" then
    for row in ← array rows 4096 do
      let x ← integer row
      let b := equation.a₁ * x + equation.a₃
      let c := x ^ 3 + equation.a₂ * x ^ 2 + equation.a₄ * x + equation.a₆
      let y := (-b + Int.sqrt (b ^ 2 + 4 * c)) / 2
      integralCoordinates := (integralCoordinates.push (x, y)).push (x, -y - b)
  unless integralCoordinates.size ≤ 8192 do throw "Too many integral coordinates"
  let analyticWitness ← analyticWitness j
  return { equation, primeCoefficients := primeCoefficients.toList, integralCoordinates := integralCoordinates.toList, analyticWitness }

/-- Bounded local parsing, with optional metadata and no analytic witness search. -/
def parse (text : String) : Except String CurveDataWitness := do
  unless text.utf8ByteSize ≤ 2 * 1024 * 1024 do throw "Witness exceeds 2 MiB"
  decode (← Json.parse text)

end VerifiedLcalc.CurveDataJson
