import VerifiedLcalc.Certificate.Json

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
