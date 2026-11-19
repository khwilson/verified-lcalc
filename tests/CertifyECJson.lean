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
