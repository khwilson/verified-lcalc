module

public import VerifiedLcalc.Verification.CurveData
public import VerifiedLcalc.Certificate.Json
public import Mathlib.Data.Int.Sqrt

/-! Field-driven decoding of untrusted elliptic-curve data. Supported fields
are decoded exactly; mathematical claims are checked separately in the kernel.
Unknown metadata does not become a theorem. -/

@[expose] public section
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

/-- Look up an object field, preserving an explicit JSON null. -/
def optional (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

/-- Optional aggregate fields use JSON null for `none`. -/
def optionalData (j : Json) (key : String) : Option Json :=
  (optional j key).bind fun value => if value == .null then none else some value

/-- Read the five integral Weierstrass coefficients in order. -/
def ainvs (j : Json) : Except String (List Int) := do
  let a ← array j 5
  unless a.size == 5 do throw "Expected five Weierstrass coefficients"
  a.toList.mapM integer

/-- Assemble an integral Weierstrass equation from its five coefficients in order. -/
def equationOfAinvs (a : List Int) : Except String (WeierstrassCurve ℤ) := do
  let [a₁, a₂, a₃, a₄, a₆] := a | throw "Expected five coefficients"
  return ⟨a₁, a₂, a₃, a₄, a₆⟩

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
  equationOfAinvs a

/-- Keep only a supported object's required fields; extra metadata is not a claim. -/
def project? (j : Json) (keys : List String) : Option Json := do
  let fields ← keys.mapM fun key => do
    return (key, ← optional j key)
  return Json.mkObj fields

/-- Select the supported fields of a Tate transcript. -/
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

/-- Decode a complete central or derivative witness when present. -/
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

/-- A complete native p-adic row pasted beside the curve coefficients. -/
def hasFlatStoredPadicRegulator (j : Json) : Bool :=
  ["lmfdb_iso", "p", "prec", "val", "unit"].all fun key => (optionalData j key).isSome

/-- Decode a field when it is present and non-null. -/
def optionalValue (j : Json) (key : String) (decode : Json → Except String α) :
    Except String (Option α) := do
  match optionalData j key with
  | none => return none
  | some value => return some (← decode value)

/-- Read an exact integer and reject negative values. -/
def nonnegativeInteger (j : Json) : Except String Nat := do
  let n ← integer j
  unless 0 ≤ n do throw "Expected a nonnegative integer"
  return n.toNat

/-- Decode the native prime dictionary, preserving unknown and additive markers. -/
def iwasawaDataClaims (j : Json) : Except String (List (ℕ × Sum String (List ℕ))) := do
  let entries := (← j.getObj?).toList
  unless entries.length ≤ 256 do throw "Oversized Iwasawa dictionary"
  entries.mapM fun (key, value) => do
    let some p := key.toNat? | throw "Expected an Iwasawa prime key"
    unless 2 ≤ p && key == toString p do throw "Expected a canonical Iwasawa prime key"
    match value with
    | .str marker =>
      unless ["a", "o?", "s?"].contains marker do throw "Unknown Iwasawa status marker"
      return (p, .inl marker)
    | _ =>
      let values ← array value 3
      unless values.size == 2 || values.size == 3 do throw "Expected two or three invariants"
      return (p, .inr (← values.toList.mapM nonnegativeInteger))

/-- Read the four b-invariants in order. -/
def bValues (j : Json) : Except String (Int × Int × Int × Int) := do
  let xs ← array j 4
  unless xs.size == 4 do throw "Expected b2,b4,b6,b8"
  return (← integer xs[0]!, ← integer xs[1]!, ← integer xs[2]!, ← integer xs[3]!)

/-- Read the two c-invariants in order. -/
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

/-- Optional data fields that identify a top-level local reduction row. -/
def localReductionFields : List String :=
  ["discriminant_valuation", "j_denominator_valuation", "reduction_type", "conductor_valuation",
    "kodaira_symbol", "tamagawa_number", "root_number"]

/-- Decode the supported exact fields from one local reduction row. -/
def localReductionClaim (j : Json) : Except String LocalReductionClaim := do
  let prime ← nonnegativeInteger (← j.getObjVal? "prime")
  let discriminantValuation ← optionalValue j "discriminant_valuation" nonnegativeInteger
  let conductorValuation ← optionalValue j "conductor_valuation" nonnegativeInteger
  let jDenominatorValuation ← optionalValue j "j_denominator_valuation" nonnegativeInteger
  let reductionType ← optionalValue j "reduction_type" integer
  if let some code := reductionType then
    unless code == 0 || code == 1 || code == -1 do throw "Unsupported local reduction type"
  let kodairaSymbol ← optionalValue j "kodaira_symbol" integer
  if let some code := kodairaSymbol then
    unless code != 0 do throw "Zero is not a PARI Kodaira code"
  let tamagawaNumber ← optionalValue j "tamagawa_number" nonnegativeInteger
  let rootNumber ← optionalValue j "root_number" integer
  return {
    prime, discriminantValuation, conductorValuation, jDenominatorValuation
    reductionType, kodairaSymbol, tamagawaNumber, rootNumber }

/-- Decode a local-row list and any top-level local claim. -/
def localReductionClaims (j : Json) :
    Except String (Option (List LocalReductionClaim)) := do
  let rows ← optionalValue j "local_invariants" fun value => do
    (← array value 256).toList.mapM localReductionClaim
  if localReductionFields.any (fun key => (optionalData j key).isSome) then
    return some ((← localReductionClaim j) :: rows.getD [])
  return rows

/-- Decode an exact JSON decimal or the catalogue's Sage real-literal encoding.
The precision tag describes representation only and supplies no error bound. -/
def exactReportedDecimal (j : Json) : Except String Rat := do
  let value ← match j with
    | .num _ => pure j
    | .str text =>
      unless text.length ≤ 512 do throw "Oversized reported decimal"
      Json.parse text
    | .obj _ =>
      let kind ← nonnegativeInteger (← j.getObjVal? "__RealLiteral__")
      unless kind = 0 do throw "Unexpected real literal encoding"
      let _ ← nonnegativeInteger (← j.getObjVal? "prec")
      Json.parse (← (← j.getObjVal? "data").getStr?)
    | _ => throw "Expected a reported JSON decimal or real literal"
  let number ← value.getNum?
  unless number.exponent ≤ 512 && (toString number.mantissa).length ≤ 512 do
    throw "Oversized reported decimal"
  return (number.mantissa : Rat) / 10 ^ number.exponent

/-- Decode an explicit regulator error as an exact decimal or rational value. -/
def regulatorErrorValue (j : Json) : Except String Rat := do
  let value ← match j with
    | .str text => if text.contains '/' then rationalValue j else exactReportedDecimal j
    | .arr _ => rationalValue j
    | _ => exactReportedDecimal j
  unless 0 ≤ value do throw "Expected a nonnegative regulator error"
  return value

/-- Decode one scoped torsion growth row without reading the rational torsion order. -/
def torsionGrowthFieldClaim (j : Json) : Except String TorsionGrowthFieldClaim := do
  let coefficients ← (← array (← j.getObjVal? "field") 256).toList.mapM integer
  let degree ← nonnegativeInteger (← j.getObjVal? "degree")
  return ⟨coefficients, degree⟩

/-- Decode the height array and its optional exact error radii. -/
def canonicalHeightsClaim (j : Json) : Except String (Option CanonicalHeightsClaim) := do
  let evidence := optionalData j "heights_evidence"
  let some raw := optionalData j "heights" | do
    if evidence.isSome then throw "heights_evidence requires heights"
    return none
  let reported ← (← array raw 4096).toList.mapM exactReportedDecimal
  let errors ← evidence.mapM fun value => do
    (← array (← value.getObjVal? "errors") 4096).toList.mapM regulatorErrorValue
  return some ⟨reported, errors⟩

/-- Decode a stored regulator report and optional explicit error evidence. -/
def regulatorClaim (j : Json) : Except String (Option RegulatorClaim) := do
  let evidence := optionalData j "regulator_evidence"
  let some raw := optionalData j "regulator" | do
    if evidence.isSome then throw "regulator_evidence requires regulator"
    return none
  let reported ← exactReportedDecimal raw
  let error ← evidence.mapM fun value => do
    regulatorErrorValue (← value.getObjVal? "error")
  return some { reported, error }

/-- Decode a decimal report and its optional explicitly specified radius. -/
def decimalEnclosureClaim (j : Json) (field : String) :
    Except String (Option DecimalEnclosureClaim) := do
  let evidence := optionalData j (field ++ "_evidence")
  let some raw := optionalData j field | do
    if evidence.isSome then throw s!"{field}_evidence requires {field}"
    return none
  let reported ← exactReportedDecimal raw
  let error ← evidence.mapM fun value => do
    regulatorErrorValue (← value.getObjVal? "error")
  return some { reported, error }

/-- Decode a stored Taylor leading coefficient only with explicit error evidence. -/
def specialLValueClaim (j : Json) : Except String (Option SpecialLValueClaim) := do
  let some evidence := optionalData j "special_value_evidence" | return none
  let reported ← exactReportedDecimal (← j.getObjVal? "special_value")
  let error ← rationalValue (← evidence.getObjVal? "error")
  unless 0 ≤ error do throw "Expected a nonnegative special-value error"
  return some { reported, error }

/-- Interpret the stored JSON decimal exactly when explicit error evidence is present. -/
def abcQualityClaim (j : Json) : Except String (Option AbcQualityClaim) := do
  let some evidence := optionalData j "abc_quality_evidence" | return none
  let number ← (← j.getObjVal? "abc_quality").getNum?
  unless number.exponent ≤ 512 && (toString number.mantissa).length ≤ 512 do
    throw "Oversized abc_quality decimal"
  let reported : Rat := (number.mantissa : Rat) / 10 ^ number.exponent
  let error ← rationalValue (← evidence.getObjVal? "error")
  let rows ← array (← evidence.getObjVal? "factors") 4096
  let factors ← rows.toList.mapM nonnegativeInteger
  return some { reported, error, factors }

/-- Decode exact raw data for one rational isogeny edge. -/
def isogenyEdgeClaim (j : Json) : Except String IsogenyEdgeClaim := do
  let target ← equation (← j.getObjVal? "target")
  let degree ← nonnegativeInteger (← j.getObjVal? "degree")
  let kernelX ← optionalValue j "kernel_x" rationalValue
  return { target, degree, kernelX }

/-- The inline analytic format owns its `rank` field. A nested analytic witness
can coexist with top-level LMFDB algebraic data. -/
def inlineAnalyticRankField (j : Json) : Bool :=
  (optionalData j "schema" == some (.str "lcalc.ec-rank.v1")) ||
    ["subject", "parameters", "coefficients", "enclosure", "evaluator"].all
      (fun key => (optionalData j key).isSome)

/-- Decode a top-level algebraic rank and check that any two spellings agree. -/
def algebraicRankClaim (j : Json) : Except String (Option Nat) := do
  let explicit ← optionalValue j "algebraic_rank" nonnegativeInteger
  if inlineAnalyticRankField j then return explicit
  let native ← optionalValue j "rank" nonnegativeInteger
  if let (some a, some b) := (explicit, native) then
    unless a = b do throw "Conflicting algebraic rank claims"
  return explicit.or native

/-- Decode the finite generator report with its stated LMFDB reduction modulus. -/
def adelicGeneratorsClaim (j : Json) : Except String (Option AdelicGeneratorsClaim) :=
  optionalValue j "adelic_gens" fun value => do
    if let some prime ← optionalValue j "prime" nonnegativeInteger then
      unless prime == 0 do throw "adelic_gens requires the prime-zero row"
    let level ← optionalValue j "adelic_level" nonnegativeInteger
    let labelLevel ← optionalValue j "adelic_image" fun label => do
      match (← label.getStr?).splitOn "." with
      | first :: _ :: _ => nonnegativeInteger (.str first)
      | _ => throw "Expected the level prefix of adelic_image"
    if let (some m, some n) := (level, labelLevel) then
      unless m == n do throw "Conflicting adelic_gens moduli"
    let some modulus := level.orElse (fun _ => labelLevel)
      | throw "adelic_gens requires adelic_level or adelic_image"
    let rows ← (← array value 256).toList.mapM fun row => do
      let entries ← array row 4
      unless entries.size == 4 do throw "adelic_gens requires four matrix entries per row"
      return (← nonnegativeInteger entries[0]!, ← nonnegativeInteger entries[1]!,
        ← nonnegativeInteger entries[2]!, ← nonnegativeInteger entries[3]!)
    return { modulus, rows }

/-- Decode whichever supported fields are present. Integer square-root
reconstruction supplies candidate y-coordinates for stored integral x-values;
the certifier subsequently proves every resulting curve equation. -/
def decode (j : Json) : Except String EllipticWitness := do
  let _ ← j.getObj?
  let equation ← equation j
  let isogenyEdge ← optionalValue j "isogeny_edge" isogenyEdgeClaim
  let classSize ← optionalValue j "class_size" nonnegativeInteger
  let classDegree ← optionalValue j "class_deg" nonnegativeInteger
  let isogenyMatrix ← optionalValue j "isogeny_matrix" fun value => do
    (← array value 128).toList.mapM fun row => do
      (← array row 128).toList.mapM nonnegativeInteger
  let isogenyDegrees ← optionalValue j "isogeny_degrees" fun value => do
    (← array value 128).toList.mapM nonnegativeInteger
  let nonmaxPrimes ← optionalValue j "nonmax_primes" fun value => do
    (← array value 256).toList.mapM nonnegativeInteger
  let nonmaxRadical ← optionalValue j "nonmax_rad" nonnegativeInteger
  let adelicGenerators ← adelicGeneratorsClaim j
  let adelicLevel ← optionalValue j "adelic_level" nonnegativeInteger
  let adelicIndex ← optionalValue j "adelic_index" nonnegativeInteger
  let adelicGenus ← optionalValue j "adelic_genus" nonnegativeInteger
  let adelicImage ← optionalValue j "adelic_image" fun value => do
    let prime ← optionalValue j "prime" nonnegativeInteger
    let some p := prime.or (if adelicGenerators.isSome then some 0 else none)
      | throw "adelic_image requires the prime-zero row"
    return (p, ← value.getStr?)
  let modPrimeImage ← optionalValue j "modell_image" fun value => do
    let some prime ← optionalValue j "prime" nonnegativeInteger
      | throw "modell_image requires the prime of the residual row"
    return (prime, ← value.getStr?)
  let modPrimeImages ← optionalValue j "modell_images" fun value => do
    (← array value 256).toList.mapM Json.getStr?
  let catalogueAnalyticRank ← optionalValue j "analytic_rank" nonnegativeInteger
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
  let integralFiberRoots ← optionalValue j "xcoord_integral_points" fun rows => do
    (← array rows 4096).toList.mapM fun row => do
      let x ← integer row
      let b := equation.a₁ * x + equation.a₃
      let c := x ^ 3 + equation.a₂ * x ^ 2 + equation.a₄ * x + equation.a₆
      return (x, (-b + Int.sqrt (b ^ 2 + 4 * c)) / 2)
  for (x, y) in integralFiberRoots.getD [] do
    let b := equation.a₁ * x + equation.a₃
    integralCoordinates := (integralCoordinates.push (x, y)).push (x, -y - b)
  unless integralCoordinates.size ≤ 8192 do throw "Too many integral coordinates"
  let numIntegralPoints ← optionalValue j "num_int_pts" nonnegativeInteger
  let generatorCoordinates ← optionalValue j "gens" weightedCoordinates
  let generatorCount ← optionalValue j "ngens" nonnegativeInteger
  let algebraicRank ← algebraicRankClaim j
  let algebraicRankBounds ← optionalValue j "rank_bounds" fun value => do
    let endpoints ← array value 2
    unless endpoints.size = 2 do throw "Expected two algebraic rank bounds"
    return (← nonnegativeInteger endpoints[0]!, ← nonnegativeInteger endpoints[1]!)
  let torsionGeneratorCoordinates ← optionalValue j "torsion_generators" weightedCoordinates
  let torsionGeneratorOrders ← optionalValue j "torsion_generator_orders" fun value => do
    (← array value 4096).toList.mapM nonnegativeInteger
  let torsionStructure ← optionalValue j "torsion_structure" fun value => do
    (← array value 16).toList.mapM nonnegativeInteger
  let torsionPrimes ← optionalValue j "torsion_primes" fun value => do
    (← array value 16).toList.mapM nonnegativeInteger
  let numeric ← numericFields j
  let base := numeric.getD { equation }
  let primeData := if (optionalData j "ap").isSome || (optionalData j "aplist").isSome
    then some primeCoefficients.toList else none
  let pointData :=
    if (optionalData j "integral_points").isSome ||
        integralFiberRoots.isSome then
      some integralCoordinates.toList
    else none
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
  let independentGeneratorPoints ← indices "independent_generator_points"
  let bInvariants ← optionalValue j "binvs" bValues
  let cInvariants ← optionalValue j "cinvs" cValues
  let discriminant ← optionalValue j "discriminant" integer
  let jInvariant ← optionalValue j "jinv" rationalValue
  let lmfdbNumber ← optionalValue j "lmfdb_number" nonnegativeInteger
  let isoNlabel ← optionalValue j "iso_nlabel" nonnegativeInteger
  let lmfdbIso ← optionalValue j "lmfdb_iso" Json.getStr?
  let lmfdbLabel ← optionalValue j "lmfdb_label" Json.getStr?
  let traceHash ← optionalValue j "trace_hash" integer
  let cremonaIso ← optionalValue j "Ciso" Json.getStr?
  let cremonaLabel ← optionalValue j "Clabel" Json.getStr?
  let cremonaNumber ← optionalValue j "Cnumber" nonnegativeInteger
  let abcQuality ← abcQualityClaim j
  let complexMultiplication ← optionalValue j "cm" integer
  let minimumTwistEquation ← optionalValue j "min_quad_twist_ainvs" fun value => do
    equationOfAinvs (← ainvs value)
  let minimumTwistDiscriminant ← optionalValue j "min_quad_twist_disc" integer
  let modifiedSzpiroRatio ← decimalEnclosureClaim j "szpiro_ratio"
  let torsionGrowthField ← optionalValue j "torsion_growth" torsionGrowthFieldClaim
  let canonicalHeights ← canonicalHeightsClaim j
  let regulator ← regulatorClaim j
  let modularDegree ← optionalValue j "degree" nonnegativeInteger
  let maninConstant ← optionalValue j "manin_constant" nonnegativeInteger
  let optimality ← optionalValue j "optimality" nonnegativeInteger
  let area ← decimalEnclosureClaim j "area"
  let faltingsHeight ← decimalEnclosureClaim j "faltings_height"
  let stableFaltingsHeight ← decimalEnclosureClaim j "stable_faltings_height"
  let faltingsIndex ← optionalValue j "faltings_index" nonnegativeInteger
  let faltingsRatio ← optionalValue j "faltings_ratio" nonnegativeInteger
  let iwasawaData ← optionalValue j "iwdata" iwasawaDataClaims
  let iwasawaThreshold ← optionalValue j "iwp0" nonnegativeInteger
  let nested ← optionalValue j "padic_regulator" pure
  let flat := hasFlatStoredPadicRegulator j
  if flat && nested.isSome then
    throw "Supply exactly one complete stored p-adic regulator row"
  let row := if flat then some j else nested
  let padicRegulator ← row.mapM fun report => do
    return {
      p := ← nonnegativeInteger (← report.getObjVal? "p")
      prec := ← integer (← report.getObjVal? "prec")
      val := ← integer (← report.getObjVal? "val")
      unit := ← integer (← report.getObjVal? "unit") }
  let padicRegulatorClassLabel ← row.mapM fun report =>
    optionalValue report "lmfdb_iso" Json.getStr?
  let realPeriod ← decimalEnclosureClaim j "real_period"
  let tamagawaProduct ← optionalValue j "tamagawa_product" nonnegativeInteger
  let analyticSha ← decimalEnclosureClaim j "sha_an"
  let sha ← optionalValue j "sha" nonnegativeInteger
  let shaPrimes ← optionalValue j "sha_primes" fun value => do
    (← array value 256).toList.mapM nonnegativeInteger
  let specialLValue ← specialLValueClaim j
  let jIntegral ← optionalValue j "j_integral" Json.getBool?
  let potentialGoodReduction ← optionalValue j "potential_good_reduction" Json.getBool?
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
  let semistable ← optionalValue j "semistable" Json.getBool?
  let squarefreeDiscriminant ← optionalValue j "squarefree_disc" Json.getBool?
  let localInvariants ← localReductionClaims j
  let intrinsicTorsion ← optionalValue j "intrinsic_torsion" nonnegativeInteger
  let torsion ← optionalValue j "torsion" nonnegativeInteger
  let torsionBound ← optionalValue j "torsion_bound" fun value => do
    let firstPrime ← nonnegativeInteger (← value.getObjVal? "first_prime")
    let secondPrime ← nonnegativeInteger (← value.getObjVal? "second_prime")
    unless firstPrime ≤ 10000 && secondPrime ≤ 10000 do
      throw "Torsion-bound prime outside supported profile"
    let bound ← nonnegativeInteger (← value.getObjVal? "bound")
    return ({ firstPrime, secondPrime, bound } : TorsionBoundWitness)
  return { base with
    equation
    specialLValue
    isogenyEdge
    classSize
    classDegree
    isogenyMatrix
    isogenyDegrees
    lmfdbNumber
    isoNlabel
    lmfdbIso := if flat then none else lmfdbIso
    lmfdbLabel
    traceHash
    cremonaIso
    cremonaLabel
    cremonaNumber
    catalogueAnalyticRank
    nonmaxPrimes
    nonmaxRadical
    adelicGenerators
    adelicLevel
    adelicIndex
    adelicGenus
    adelicImage
    modPrimeImage
    modPrimeImages
    bInvariants
    cInvariants
    discriminant
    jInvariant
    abcQuality
    complexMultiplication
    minimumTwistEquation
    minimumTwistDiscriminant
    modifiedSzpiroRatio
    torsionGrowthField
    canonicalHeights
    regulator
    modularDegree
    maninConstant
    optimality
    area
    faltingsHeight
    stableFaltingsHeight
    faltingsIndex
    faltingsRatio
    iwasawaData
    iwasawaThreshold
    padicRegulator
    padicRegulatorClassLabel := padicRegulatorClassLabel.join
    realPeriod
    tamagawaProduct
    analyticSha
    sha
    shaPrimes
    jIntegral
    potentialGoodReduction
    discriminantSign
    minimalDiscriminantAbs
    conductor
    rootNumber
    dirichletCoefficients
    badPrimes
    numBadPrimes
    semistable
    squarefreeDiscriminant
    localInvariants
    torsionBound
    intrinsicTorsion
    torsion
    primeCoefficients := primeData
    integralCoordinates := pointData
    integralFiberRoots
    numIntegralPoints
    generatorCoordinates
    generatorCount
    algebraicRank
    algebraicRankBounds
    torsionGeneratorCoordinates
    torsionGeneratorOrders
    torsionStructure
    torsionPrimes
    infiniteOrderPoints
    independentPoints
    independentGeneratorPoints
    minimality
    localData }

/-- Bounded local parsing, with optional metadata and no analytic witness search. -/
def parse (text : String) : Except String EllipticWitness := do
  unless text.utf8ByteSize ≤ 2 * 1024 * 1024 do throw "Witness exceeds 2 MiB"
  decode (← Json.parse text)

end VerifiedLcalc.CurveDataJson
