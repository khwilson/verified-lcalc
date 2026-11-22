import VerifiedLcalc.Certificate.Json
import VerifiedLcalc.Certificate.CurveDataJson

/-! # Validate the supported elliptic-curve JSON schema

These checks cover data decoding separately from the mathematical certificate
proofs, including rejection of malformed rank, conductor and schema fields.
-/

-- Schema checks are data validation, independent of the mathematical certificates.
#eval do
  let text ← IO.FS.readFile "data/witnesses/11a1.json"
  let bad := [
    text.replace "\"rank\": \"0\"" "\"rank\": \"4\"",
    text.replace "\"conductor\": \"11\"" "\"conductor\": 11",
    text.replace "\"conductor\": \"11\"" "\"conductor\": \"011\"",
    text.replace "\"schema\":" "\"unexpected\": true, \"schema\":",
    text.replace "\"steps_per_unit\": \"0\"" "\"steps_per_unit\": \"1\""
  ]
  for input in bad do
    match VerifiedLcalc.CertificateJson.parse input with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "Malformed or unsupported JSON was accepted")

-- The supported 128-term, 106-bit profile has exact fractions far larger than
-- ordinary curve coefficients. Parse them exactly without relaxing integer caps.
#eval show IO Unit from do
  let n : Int := 2 ^ 2048 + 1
  let d : Nat := 2 ^ 4096
  let expected : Rat := (n : Rat) / d
  match VerifiedLcalc.CertificateJson.rational (.str s!"{n}/{d}") with
  | .ok value =>
    unless value == expected do throw (IO.userError "Large fraction changed value")
  | .error reason => throw (IO.userError reason)
  let oversized := String.ofList (List.replicate 8193 '9')
  for text in ["1/0", "1/-2", "01/2", "-0/2", oversized ++ "/1"] do
    match VerifiedLcalc.CertificateJson.rational (.str text) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "Noncanonical or oversized fraction was accepted")
  match VerifiedLcalc.CertificateJson.decimal (.str (String.ofList (List.replicate 513 '9'))) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Ordinary coefficient integer bound was relaxed")

-- Catalogue real literals preserve their decimal payload exactly. Their `prec`
-- field is representation metadata, not an implicit error certificate.
#eval show IO Unit from do
  let parse := fun text => match Lean.Json.parse text with
    | .ok value => value
    | .error reason => panic! reason
  let literal := parse "{\"__RealLiteral__\":0,\"data\":\"1.000000000000\",\"prec\":97}"
  match VerifiedLcalc.CurveDataJson.exactReportedDecimal literal with
  | .ok value => unless value == 1 do throw (IO.userError "Real literal decimal changed value")
  | .error reason => throw (IO.userError reason)
  match VerifiedLcalc.CurveDataJson.exactReportedDecimal (.str "1.000") with
  | .ok value => unless value == 1 do throw (IO.userError "Decimal string changed value")
  | .error reason => throw (IO.userError reason)
  match VerifiedLcalc.CurveDataJson.exactReportedDecimal (.str "1/1") with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Malformed decimal string was accepted")
  let exact := parse "{\"regulator\":{\"__RealLiteral__\":0,\"data\":\"1.0\",\"prec\":97}}"
  match VerifiedLcalc.CurveDataJson.regulatorClaim exact with
  | .ok (some claim) =>
    unless claim.reported == 1 && claim.error.isNone do
      throw (IO.userError "Exact rank-zero regulator claim was changed")
  | .ok none => throw (IO.userError "Regulator claim was dropped")
  | .error reason => throw (IO.userError reason)
  let bounded := parse "{\"regulator\":0.999,\"regulator_evidence\":{\"error\":0.001}}"
  match VerifiedLcalc.CurveDataJson.regulatorClaim bounded with
  | .ok (some claim) =>
    unless claim.reported == 999 / 1000 && claim.error == some (1 / 1000) do
      throw (IO.userError "Decimal regulator enclosure changed value")
  | .ok none => throw (IO.userError "Bounded regulator claim was dropped")
  | .error reason => throw (IO.userError reason)
  let fractionBound := parse "{\"regulator\":1,\"regulator_evidence\":{\"error\":\"1/1000\"}}"
  match VerifiedLcalc.CurveDataJson.regulatorClaim fractionBound with
  | .ok (some claim) =>
    unless claim.error == some (1 / 1000) do
      throw (IO.userError "Rational regulator error changed value")
  | .ok none => throw (IO.userError "Rational-error regulator claim was dropped")
  | .error reason => throw (IO.userError reason)
  let bad := parse "{\"regulator\":1,\"regulator_evidence\":{\"error\":-0.1}}"
  match VerifiedLcalc.CurveDataJson.regulatorClaim bad with
  | .error _ => pure ()
  | _ => throw (IO.userError "Negative regulator error was accepted")
