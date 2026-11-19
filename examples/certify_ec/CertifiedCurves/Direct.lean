module
public import VerifiedLcalc.Tactic.CertifyEC
@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open VerifiedLcalc VerifiedLcalc.EllipticCurve

-- Supplied data only. No JSON file, witness search, or numerical producer.
certify_ec DirectCurve from EllipticWitness.central
  { equation := ⟨0,-1,1,-10,-20⟩
    conductor := 11
    rootNumber := 1
    policy := ⟨53⟩
    termLimit := 1
    coefficients := [1]
    alphaLo := ((5397215081808807583435051761664 : Rat) / 2848959001535859775543212890625)
    alphaHi := ((337325942613050473965764476928 : Rat) / 178059937595991230010986328125)
    geometricUpper := ((169336229459221 : Rat) / 1125899906842624)
    tail := ((28674758607465946046101926841 : Rat) / 104834424879811077321286221824)
    box := ⟨((366028917649787835048376743221 : Rat) / 13418806384615817897124636393472),((963345890145134125303004031503 : Rat) / 1677350798076977237140579549184),((0 : Rat) / 1),((0 : Rat) / 1)⟩ }
  ⟨[11,11,11,11,11]⟩
  ⟨none, none⟩
