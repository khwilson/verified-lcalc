import LcalcVolunteer.Witness
open LcalcVolunteer
/-- CLI for local contributors and the server's independent reconstruction. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["compute",line] => IO.println (run line); return 0
  | ["render",line,name,path] =>
    if !(name.startsWith "LcalcCertificates.C") ||
        !(name.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then return 2
    let some candidate := decodeWitness line | IO.eprintln "invalid witness transport"; return 4
    IO.FS.writeFile path (proofSource name candidate)
    return 0
  | ["prove",line,name,path] =>
    if !(name.startsWith "LcalcCertificates.C") ||
        !(name.toList.all fun c => c.isAlphanum || c == '.' || c == '_') then return 2
    let some candidate := decode line >>= compute | IO.eprintln "inconclusive"; return 3
    IO.FS.writeFile path (proofSource name candidate)
    IO.println (encode candidate)
    return 0
  | _ => IO.eprintln "Usage: certificate-worker compute LINE | prove LINE MODULE SOURCE_PATH"; return 2
