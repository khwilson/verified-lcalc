module
public import LcalcVolunteer.Core
@[expose] public section
namespace LcalcVolunteer
open VerifiedLcalc VerifiedLcalc.EllipticCurve

def flat [Repr α] (x : α) : String := (reprStr x).replace "\n" " "

/-- Indent Lean's pretty representation without changing its expressions. -/
def indented [Repr α] (x : α) : String :=
  String.intercalate "\n" ((reprStr x).splitOn "\n" |>.map ("  " ++ ·))

/-- Trusted template: all interpolated data are typed Lean values.
The file exports named theorems; it remains an unchecked candidate until compiled. -/
def proofSource (name : String) (c : Candidate) : String := Id.run do
  let header := "module\n\npublic import VerifiedLcalc.Assumptions.DerivativeCertification\n\n@[expose] public section\n\n/-!\n# Elliptic curve analytic-rank certificate\n\nGenerated proof candidate: compile with the recorded Lean environment before use.\nThe analytic-rank theorem depends on the explicit ellipticModularity assumption.\nImport this module and use `curve_analytic_rank` (explicit curve) or\n`analytic_rank` (certificate result). All witness checks are named theorems.\n-/\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\nset_option pp.fullNames true\n\nnamespace " ++ name ++ "\n\nopen VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions\n\n"
  let (equation,data,payload,proof,rank) := match c.value with
    | .central r =>
      let rem := (squareTailBound r.geometricUpper r.termLimit).getD 0
      (r.equation,
       "def result : CentralResult :=\n" ++ indented r ++ "\n\n",
       "theorem payload_correct : CentralPayloadCorrect result := by\n  unfold CentralPayloadCorrect\n  exact ⟨by decide +kernel,\n    by decide +kernel,\n    by decide +kernel,\n    by decide +kernel,\n    by decide +kernel,\n    by decide +kernel,\n    " ++ flat rem ++ ",\n    by decide +kernel,\n    by decide +kernel,\n    by decide +kernel⟩\n\n",
       "certifyWildCentralModel result nonsingular\n    minimality minimality_valid localData local_data_valid\n    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)",0)
    | .derivative r =>
      (r.equation,
       "def result : DerivativeResult :=\n" ++ indented r ++ "\n\n",
       "theorem payload_correct : DerivativePayloadCorrect result := by\n  decide +kernel\n\n",
       "certifyDerivativeModel result nonsingular\n    minimality minimality_valid localData local_data_valid\n    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)",1)
  let curve := "/-- The exact Weierstrass equation, independent of numerical witness fields. -/\ndef curve : Artifacts.CurveEquation :=\n" ++ indented equation ++ "\n\n"
  let arithmetic := "def minimality : MinimalityWitness :=\n" ++ indented c.minimality ++ "\n\n" ++
    "def localData : WildData :=\n" ++ indented c.localData ++ "\n\n" ++
    "theorem nonsingular : discriminant result.equation ≠ 0 := by\n  decide +kernel\n\n" ++
    "theorem minimality_valid : minimality.Valid result.equation := by\n  decide +kernel\n\n" ++
    "theorem local_data_valid : localData.Valid result.equation := by\n  decide +kernel\n\n"
  let rankType := "analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = " ++ toString rank
  return header ++ curve ++ data ++ arithmetic ++ payload ++
    "/-- Analytic rank of the certificate's curve, conditional on ellipticModularity. -/\ntheorem analytic_rank :\n    " ++ rankType ++ " :=\n  " ++ proof ++ "\n\n" ++
    "theorem curve_nonsingular : discriminant curve ≠ 0 :=\n  nonsingular\n\n" ++
    "/-- Public theorem for use after importing this module. -/\ntheorem curve_analytic_rank :\n    analyticOrderAt (modularWitness curve curve_nonsingular).formL (1 : ℂ) = " ++ toString rank ++ " :=\n  analytic_rank\n\n" ++
    "def certifiedRank :\n    {n : ℕ // analyticOrderAt (modularWitness curve curve_nonsingular).formL (1 : ℂ) = n} :=\n  ⟨" ++ toString rank ++ ", curve_analytic_rank⟩\n\n" ++
    "#print axioms payload_correct\n#print axioms minimality_valid\n#print axioms local_data_valid\n#print axioms analytic_rank\n\nend " ++ name ++ "\n"
end LcalcVolunteer
