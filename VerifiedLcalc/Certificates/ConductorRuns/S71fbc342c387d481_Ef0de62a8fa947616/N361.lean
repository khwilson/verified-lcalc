module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -13718, a6 := -619025 }
def label : String := "361.a1"
def inputConductor : Nat := 361
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 19, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 361 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -13718, a6 := -619025 },   conductor := 361,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -1, 0, 3, 0, -3, 0, -5, 0, 0, 0, 0, 4, -7, 0, 0, 2, 0, 0, -4, 0, -4, 0, 0, -6, 0, 0, 0,                    0, 0, 0, -3, 6, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16320875724800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/950000000000000000000,   finite := ((2982945352239299 : Rat)/2251799813685248, (31609645236974545 : Rat)/9007199254740992),   tail := (370174258734831975334231500899791717529296875 : Rat)/728986896522283624658067958065634188084641792,   box := { reLo := (156109424770614983148036187776640712723196974443949 : Rat)/191099541001937518502364566799157608601260337922048,            reHi := (3070716104571839770704891514645515182300179597815295 : Rat)/764398164007750074009458267196630434405041351688192,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 0, a3 := 1, a4 := -38, a6 := 90 }
def label : String := "361.a2"
def inputConductor : Nat := 361
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 361 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -38, a6 := 90 },   conductor := 361,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, 0, -2, -1, 0, 3, 0, -3, 0, -5, 0, 0, 0, 0, 4, -7, 0, 0, 2, 0, 0, -4, 0, -4, 0, 0, -6, 0, 0, 0,                    0, 0, 0, -3, 6, 0, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16320875724800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/950000000000000000000,   finite := ((2982945352239299 : Rat)/2251799813685248, (31609645236974545 : Rat)/9007199254740992),   tail := (370174258734831975334231500899791717529296875 : Rat)/728986896522283624658067958065634188084641792,   box := { reLo := (156109424770614983148036187776640712723196974443949 : Rat)/191099541001937518502364566799157608601260337922048,            reHi := (3070716104571839770704891514645515182300179597815295 : Rat)/764398164007750074009458267196630434405041351688192,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -277729, a6 := 56427893 }
def label : String := "361.b1"
def inputConductor : Nat := 361
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 361 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -277729, a6 := 56427893 },   conductor := 361,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, -2, 3, 0, -1, 0, 1, 0, 3, -4, 4, 0, 6, 4, -3, 0, 0, -6, -2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16320875724800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/950000000000000000000,   geometricUpper := (6470997121412007 : Rat)/9007199254740992,   tail := (73458186147368600474024395812816817233596762921812579999919885246836218433087352714517759452127432935937639812280265211020477208620310922891529391264904275915488446264093727640370308425592281112712234816956759555603846706905178980057775984611554251647392690329751085585735356638216299880342906514290803365665698299169916935269769578807238513020838062018555950245920735058373635158678624187578440234375 : Rat)/51027549743883935405993109223448030295948513045567077206431798489592896258176963734810396797798168234979890692965071340104632660353254086493383691971973887726662186651131482402203124543364308041807617713662598455903352859193291593199906108599632762262333347655838540616719496617581491275342220533454788130297349269842450910027226049870540360499532832267320275614870858135882065306701349763382996107264,   box := { reLo := (46080072641852099423880781848168332480256801509549487946606684484821972653613921871413780402730492843018554973564273495585812657282271258157850078499435252481833166396652467806594139150597183683651103389192571197749640858766484185401954335216149455863098183716117949917632447529838538237756714352060443382373657464481502316758462661893402982102887504848246626493052278247408508869052986314776266207927837 : Rat)/101493796440585147522520294245438132258641592447632916563592847195800270657513980868537879230820556619375002588307526895468114361442622378035340163332256062688331089249100518497982014716751608695155351632474908328791768836935456978874613250004669564139781028487462857286655078772369586146655676641041573591161427697716634860044152613192504777033570803379700028197978136832269427895028984679368779257348096,            reHi := (6202106847494882917920047981503773615419758423523157682257449675814433276224910946164900932639502476096497740367301519636129587312223118343953033086838330251887723111779754037950819366292877877043035454045603412963680156642089740375458541414789162314737914198435247531806947700171310199123333920332779711845746911564000352558490478528420713729157871700630149333800626325922160840668767268836647466998989463 : Rat)/1860719601410727704579538727833032424741762528206603470332535531923004962054422982589861119231710204688541714118971326416915429959781410263981236327758027815952736636233509505796336936473779492744514779928706652694515762010483377946034576250085608675895985522270152383588676444160109079355354071752428849171292841124804972434142797908529254245615464728627833850296265841924939511408864719121760953051381760,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (73458186147368600474024395812816817233596762921812579999919885246836218433087352714517759452127432935937639812280265211020477208620310922891529391264904275915488446264093727640370308425592281112712234816956759555603846706905178980057775984611554251647392690329751085585735356638216299880342906514290803365665698299169916935269769578807238513020838062018555950245920735058373635158678624187578440234375 : Rat)/102055099487767870811986218446896060591897026091134154412863596979185792516353927469620793595596336469959781385930142680209265320706508172986767383943947775453324373302262964804406249086728616083615235427325196911806705718386583186399812217199265524524666695311677081233438993235162982550684441066909576260594698539684901820054452099741080720999065664534640551229741716271764130613402699526765992214528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3369, a6 := 81208 }
def label : String := "361.b2"
def inputConductor : Nat := 361
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 19, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 361 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -3369, a6 := 81208 },   conductor := 361,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, -2, 3, 0, -1, 0, 1, 0, 3, -4, 4, 0, 6, 4, -3, 0, 0, -6, -2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16320875724800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/950000000000000000000,   geometricUpper := (6470997121412007 : Rat)/9007199254740992,   tail := (73458186147368600474024395812816817233596762921812579999919885246836218433087352714517759452127432935937639812280265211020477208620310922891529391264904275915488446264093727640370308425592281112712234816956759555603846706905178980057775984611554251647392690329751085585735356638216299880342906514290803365665698299169916935269769578807238513020838062018555950245920735058373635158678624187578440234375 : Rat)/51027549743883935405993109223448030295948513045567077206431798489592896258176963734810396797798168234979890692965071340104632660353254086493383691971973887726662186651131482402203124543364308041807617713662598455903352859193291593199906108599632762262333347655838540616719496617581491275342220533454788130297349269842450910027226049870540360499532832267320275614870858135882065306701349763382996107264,   box := { reLo := (46080072641852099423880781848168332480256801509549487946606684484821972653613921871413780402730492843018554973564273495585812657282271258157850078499435252481833166396652467806594139150597183683651103389192571197749640858766484185401954335216149455863098183716117949917632447529838538237756714352060443382373657464481502316758462661893402982102887504848246626493052278247408508869052986314776266207927837 : Rat)/101493796440585147522520294245438132258641592447632916563592847195800270657513980868537879230820556619375002588307526895468114361442622378035340163332256062688331089249100518497982014716751608695155351632474908328791768836935456978874613250004669564139781028487462857286655078772369586146655676641041573591161427697716634860044152613192504777033570803379700028197978136832269427895028984679368779257348096,            reHi := (6202106847494882917920047981503773615419758423523157682257449675814433276224910946164900932639502476096497740367301519636129587312223118343953033086838330251887723111779754037950819366292877877043035454045603412963680156642089740375458541414789162314737914198435247531806947700171310199123333920332779711845746911564000352558490478528420713729157871700630149333800626325922160840668767268836647466998989463 : Rat)/1860719601410727704579538727833032424741762528206603470332535531923004962054422982589861119231710204688541714118971326416915429959781410263981236327758027815952736636233509505796336936473779492744514779928706652694515762010483377946034576250085608675895985522270152383588676444160109079355354071752428849171292841124804972434142797908529254245615464728627833850296265841924939511408864719121760953051381760,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (73458186147368600474024395812816817233596762921812579999919885246836218433087352714517759452127432935937639812280265211020477208620310922891529391264904275915488446264093727640370308425592281112712234816956759555603846706905178980057775984611554251647392690329751085585735356638216299880342906514290803365665698299169916935269769578807238513020838062018555950245920735058373635158678624187578440234375 : Rat)/102055099487767870811986218446896060591897026091134154412863596979185792516353927469620793595596336469959781385930142680209265320706508172986767383943947775453324373302262964804406249086728616083615235427325196911806705718386583186399812217199265524524666695311677081233438993235162982550684441066909576260594698539684901820054452099741080720999065664534640551229741716271764130613402699526765992214528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 1, a4 := 241, a6 := -17 }
def label : String := "361.b3"
def inputConductor : Nat := 361
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.nonsingular
def minimality : MinimalityWitness := { primes := [19, 19, 19, 19, 19, 19, 19] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.globally_minimal
def localData : WildData := { atTwo := none, atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 361 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 241, a6 := -17 },   conductor := 361,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 2, -2, 3, 0, -1, 0, 1, 0, 3, -4, 4, 0, 6, 4, -3, 0, 0, -6, -2, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16320875724800000095367431640625,   alphaHi := (314159265358979323847 : Rat)/950000000000000000000,   geometricUpper := (6470997121412007 : Rat)/9007199254740992,   tail := (73458186147368600474024395812816817233596762921812579999919885246836218433087352714517759452127432935937639812280265211020477208620310922891529391264904275915488446264093727640370308425592281112712234816956759555603846706905178980057775984611554251647392690329751085585735356638216299880342906514290803365665698299169916935269769578807238513020838062018555950245920735058373635158678624187578440234375 : Rat)/51027549743883935405993109223448030295948513045567077206431798489592896258176963734810396797798168234979890692965071340104632660353254086493383691971973887726662186651131482402203124543364308041807617713662598455903352859193291593199906108599632762262333347655838540616719496617581491275342220533454788130297349269842450910027226049870540360499532832267320275614870858135882065306701349763382996107264,   box := { reLo := (46080072641852099423880781848168332480256801509549487946606684484821972653613921871413780402730492843018554973564273495585812657282271258157850078499435252481833166396652467806594139150597183683651103389192571197749640858766484185401954335216149455863098183716117949917632447529838538237756714352060443382373657464481502316758462661893402982102887504848246626493052278247408508869052986314776266207927837 : Rat)/101493796440585147522520294245438132258641592447632916563592847195800270657513980868537879230820556619375002588307526895468114361442622378035340163332256062688331089249100518497982014716751608695155351632474908328791768836935456978874613250004669564139781028487462857286655078772369586146655676641041573591161427697716634860044152613192504777033570803379700028197978136832269427895028984679368779257348096,            reHi := (6202106847494882917920047981503773615419758423523157682257449675814433276224910946164900932639502476096497740367301519636129587312223118343953033086838330251887723111779754037950819366292877877043035454045603412963680156642089740375458541414789162314737914198435247531806947700171310199123333920332779711845746911564000352558490478528420713729157871700630149333800626325922160840668767268836647466998989463 : Rat)/1860719601410727704579538727833032424741762528206603470332535531923004962054422982589861119231710204688541714118971326416915429959781410263981236327758027815952736636233509505796336936473779492744514779928706652694515762010483377946034576250085608675895985522270152383588676444160109079355354071752428849171292841124804972434142797908529254245615464728627833850296265841924939511408864719121760953051381760,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (73458186147368600474024395812816817233596762921812579999919885246836218433087352714517759452127432935937639812280265211020477208620310922891529391264904275915488446264093727640370308425592281112712234816956759555603846706905178980057775984611554251647392690329751085585735356638216299880342906514290803365665698299169916935269769578807238513020838062018555950245920735058373635158678624187578440234375 : Rat)/102055099487767870811986218446896060591897026091134154412863596979185792516353927469620793595596336469959781385930142680209265320706508172986767383943947775453324373302262964804406249086728616083615235427325196911806705718386583186399812217199265524524666695311677081233438993235162982550684441066909576260594698539684901820054452099741080720999065664534640551229741716271764130613402699526765992214528, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N361.C361_b3
