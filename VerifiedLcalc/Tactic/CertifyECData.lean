module

public import VerifiedLcalc.Certificate.CurveDataJson
public import VerifiedLcalc.Tactic.CertifyECCommon
public meta import VerifiedLcalc.Certificate.CurveDataJson

/-!
# Certifying stored prime coefficients and point membership

This module implements the arithmetic branch of the `certify_ec` command.
Import `VerifiedLcalc.Tactic.CertifyEC` for the public syntax and JSON dispatch.

`certify_ec Name from witness` accepts an `EllipticWitness` containing the
integral equation, explicit `(prime, coefficient)` pairs and integer `(x, y)`
pairs, plus rational affine pairs for the two source generator lists. All
lists are optional. `from_json "file.json"` and
`from_json_string "..."` extract the supported fields and allow unrelated
metadata. File paths are relative to the containing Lean file.
Verification performs no witness search and needs no analytic-rank certificate.

The command exports `Name.curve`, `Name.witness`, `Name.nonsingular`,
`Name.prime_coefficients_valid`, `Name.ap_correct`, `Name.integral_coordinates_valid`,
and `Name.points_on_curve`. `ap_correct p a h` proves that the actual rational
curve's `LFunction p` equals `a` when `h` proves `(p, a)` belongs to the supplied
list. It includes bad primes where the local minimality checker succeeds.

`Name.point i` constructs the rational point for an index into the supplied
integer-coordinate list; `Name.point_integral i` proves membership in TauCeti's
`curve.integralPoints`. These are membership certificates, not completeness or
algebraic-rank certificates. Every generated theorem is audited against standard
Lean axioms only. Failure rolls back the entire command. Compile the containing
module to obtain importable `.olean` declarations; use a `public section` when
exporting through Lean's `module` syntax.
-/

public meta section
namespace VerifiedLcalc.CertifyECData
open Lean Elab Command Meta

/-- Export checked affine points for one supplied rational coordinate list. -/
private def certifyRationalCoordinates (base field : Name) (curve witness : TSyntax `term) :
    CommandElabM Unit := do
  let some input ← CertifyEC.optionalInput (base.getPrefix ++ `witness) field | return
  let coords := CertifyEC.rootIdent (base ++ `coordinates)
  CertifyEC.emit (← `(def $coords : List (Rat × Rat) := $input))
  let witnessField := mkIdent field
  CertifyEC.checked (base ++ `coordinates_eq)
    (← `(($witness).$witnessField = some $coords)) (← `(by rfl))
  let valid := CertifyEC.rootIdent (base ++ `coordinates_valid)
  CertifyEC.checked (base ++ `coordinates_valid)
    (← `(EllipticWitness.affineCoordinatesValid (($curve).baseChange ℚ) $coords = true))
    (← `(by decide +kernel))
  let onCurve := CertifyEC.rootIdent (base ++ `points_on_curve)
  CertifyEC.checked (base ++ `points_on_curve)
    (← `(∀ (x y : Rat), (x, y) ∈ $coords → (($curve).baseChange ℚ).toAffine.Equation x y))
    (← `(EllipticWitness.affineCoordinatesValid_sound (($curve).baseChange ℚ) $coords $valid))
  let point := CertifyEC.rootIdent (base ++ `point)
  CertifyEC.emit (← `(def $point (i : Fin ($coords).length) :
      (($curve).baseChange ℚ).toAffine.Point :=
    .mk ($onCurve (($coords)[i]).1 (($coords)[i]).2 (List.getElem_mem i.isLt))))

/-- Check supplied arithmetic data and export ordinary definitions and theorems. -/
def certify (name : Name) (input : TSyntax `term) (announce := true) : CommandElabM Unit := do
  let name := name.eraseMacroScopes
  let base := (← getCurrNamespace) ++ name
  let w := CertifyEC.rootIdent (base ++ `witness)
  CertifyEC.emit (← `(def $w : EllipticWitness := $input))
  let curve := CertifyEC.rootIdent (base ++ `curve)
  CertifyEC.emit (← `(def $curve : WeierstrassCurve ℤ := ($w).equation))
  let hn := CertifyEC.rootIdent (base ++ `nonsingular)
  CertifyEC.checked (base ++ `nonsingular) (← `(($curve).Δ ≠ 0)) (← `(by decide +kernel))
  let hap := CertifyEC.rootIdent (base ++ `prime_coefficients_valid)
  CertifyEC.checked (base ++ `prime_coefficients_valid) (← `(($w).primeCoefficientsValid = true))
    (← `(by decide +kernel))
  CertifyEC.checked (base ++ `ap_correct)
    (← `(∀ (p : Nat) (a : Int), (p, a) ∈ ($w).primeCoefficients.getD [] →
      (($curve).baseChange ℚ).LFunction p = a))
    (← `(EllipticWitness.primeCoefficientsValid_sound $w $hn $hap))
  let hcoords := CertifyEC.rootIdent (base ++ `integral_coordinates_valid)
  CertifyEC.checked (base ++ `integral_coordinates_valid) (← `(($w).integralCoordinatesValid = true))
    (← `(by decide +kernel))
  let hpoints := CertifyEC.rootIdent (base ++ `points_on_curve)
  CertifyEC.checked (base ++ `points_on_curve)
    (← `(∀ (x y : Int), (x, y) ∈ ($w).integralCoordinates.getD [] →
      ($curve).toAffine.Equation x y))
    (← `(EllipticWitness.integralCoordinatesValid_sound $w $hcoords))
  let hi := CertifyEC.rootIdent (base ++ `curve_isElliptic)
  CertifyEC.emit (← `(instance $hi:ident : (($curve).baseChange ℚ).IsElliptic := ⟨by
    apply isUnit_iff_ne_zero.mpr
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, eq_intCast] using
      (show (($curve).Δ : ℚ) ≠ 0 by exact_mod_cast $hn)⟩))
  let point := CertifyEC.rootIdent (base ++ `point)
  CertifyEC.emit (← `(def $point (i : Fin (($w).integralCoordinates.getD []).length) :
      (($curve).baseChange ℚ).toAffine.Point :=
    ($curve).pointOfIntegralSolution ((($w).integralCoordinates.getD [])[i]).1
      ((($w).integralCoordinates.getD [])[i]).2
      ($hpoints _ _ (List.getElem_mem i.isLt))))
  CertifyEC.checked (base ++ `point_integral)
    (← `(∀ i : Fin (($w).integralCoordinates.getD []).length,
      $point i ∈ ($curve).integralPoints))
    (← `(by intro i; exact WeierstrassCurve.pointOfIntegralSolution_mem _ _ _ _))
  certifyRationalCoordinates (base ++ `generators) `generatorCoordinates curve w
  certifyRationalCoordinates (base ++ `torsion_generators) `torsionGeneratorCoordinates curve w
  if announce then logInfo m!"Certified {base}.ap_correct and {base}.point_integral (arithmetic only)"

/-- Decode data only; mathematical claims are checked by `certify`. -/
def jsonInput (text : String) : CommandElabM (TSyntax `term) := do
  match CurveDataJson.parse text with
  | .error message => throwError "Invalid curve-data JSON: {message}"
  | .ok witness => CertifyEC.literalSyntax (toExpr witness)

end VerifiedLcalc.CertifyECData
