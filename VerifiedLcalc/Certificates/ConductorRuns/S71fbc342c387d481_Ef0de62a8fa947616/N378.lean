module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 441, a6 := -1571 }
def label : String := "378.a1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 441, a6 := -1571 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, -4, 0, -1, -1, 0, 4, 4, 0, 3, 1, 0, 1, 7, 0, 2, -4, 0, -4, 1, 0, 11, -3, 0, -1, -1, 0,                    -9, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/121259495796231308852887305105441491849603586066053345354709477945025753963785163232363770828246829562320413932267640772779963243722866497809255918615872898274961178593276442354996414821045796810271651925620275987384207051569252000582340730848828386287688498794333053914148036937565425350696324612138255334409107530816348176974844331203663839539552857354758277171936435768939792910466665461465721652282402357154887345411247718546721827366503362864970096085184027734993048135907649885851466348367659095068130210718091404990480384,   box := { reLo := (1462833091127335817789675627765455533542894622108195596664431147308925250193669191834915135995958525292682578930223764982469460654452396799180428376837694586995776534363761134575117616751149365895472085057163659589440126764035050776507790623851091530686683718360740759725828732732039803438910482932655846239363176124219557523162221626294779000898901473910135832296641073421605864420028875320625872372972746932067593452893406723052175518374336428964855273012609759034881277662652074731024040357532551741991456361964364278728738351936077 : Rat)/2711244583033313925349663988584414374068550219354882664332964503947691238623137414482155290498124881341979442403576215800169608785333639987645589552753941992843906966041247179632193133879792781208971363282849593789927119608041400989328573288930148505029629487508957788124999468180096534813554292196213003031457933145641122563077676671868324694516208984627903607277364753514362128939118576586210452929310150493294483647783104665169991193020642318895389462501416146463513878069155085119599625775676592368742080357221916548832895629787136,            reHi := (66343282816114838503883749053211626203377166463651111922457326491931623282227461313969601615567077432355722065955796608443818431740032769876456910826205015366199557475477064687904955305645398466947100169661045310987107132401573708118451189522397883574784979055191385558531006137663645358924168192882712799813140376804493731785172164186430834613334838319428193924926083601731511329009726971505799102921834567600113022334080133095410088747103522489064098873688981290089053943728342954804533393682310020437030450802820085101518516751718011 : Rat)/67781114575832848133741599714610359351713755483872066608324112598692280965578435362053882262453122033549486060089405395004240219633340999691139738818848549821097674151031179490804828346994819530224284082071239844748177990201035024733214332223253712625740737187723944703124986704502413370338857304905325075786448328641028064076941916796708117362905224615697590181934118837859053223477964414655261323232753762332362091194577616629249779825516057972384736562535403661587846951728877127989990644391914809218552008930547913720822390744678400,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/242518991592462617705774610210882983699207172132106690709418955890051507927570326464727541656493659124640827864535281545559926487445732995618511837231745796549922357186552884709992829642091593620543303851240551974768414103138504001164681461697656772575376997588666107828296073875130850701392649224276510668818215061632696353949688662407327679079105714709516554343872871537879585820933330922931443304564804714309774690822495437093443654733006725729940192170368055469986096271815299771702932696735318190136260421436182809980960768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -141, a6 := 681 }
def label : String := "378.b1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -141, a6 := 681 },   conductor := 378,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, 1, -1, 0, 3, 3, 0, -4, -1, 0, 1, -6, 0, -7, -3, 0, -3, -3, 0, 4, 4, 0, 1, 0, 0,                    5, -1, 0, 6, -3, 0, -7, 7, 0, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   finite := ((4182875161045881 : Rat)/4503599627370496, (28305879756624527 : Rat)/9007199254740992),   tail := (42723341893935745735584732530307769775390625 : Rat)/72507300583803020931143369083458597517524992,   box := { reLo := (12908149507470177171361434293207253006481299543081 : Rat)/38014707608480918237947294690028341175268143005696,            reHi := (283727490467678561020684408760984805789479016536927 : Rat)/76029415216961836475894589380056682350536286011392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -96, a6 := 1088 }
def label : String := "378.b2"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -96, a6 := 1088 },   conductor := 378,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, 1, -1, 0, 3, 3, 0, -4, -1, 0, 1, -6, 0, -7, -3, 0, -3, -3, 0, 4, 4, 0, 1, 0, 0,                    5, -1, 0, 6, -3, 0, -7, 7, 0, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   finite := ((4182875161045881 : Rat)/4503599627370496, (28305879756624527 : Rat)/9007199254740992),   tail := (42723341893935745735584732530307769775390625 : Rat)/72507300583803020931143369083458597517524992,   box := { reLo := (12908149507470177171361434293207253006481299543081 : Rat)/38014707608480918237947294690028341175268143005696,            reHi := (283727490467678561020684408760984805789479016536927 : Rat)/76029415216961836475894589380056682350536286011392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 849, a6 := -25939 }
def label : String := "378.b3"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 849, a6 := -25939 },   conductor := 378,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -3, 0, 1, -1, 0, 3, 3, 0, -4, -1, 0, 1, -6, 0, -7, -3, 0, -3, -3, 0, 4, 4, 0, 1, 0, 0,                    5, -1, 0, 6, -3, 0, -7, 7, 0, 3],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   finite := ((4182875161045881 : Rat)/4503599627370496, (28305879756624527 : Rat)/9007199254740992),   tail := (42723341893935745735584732530307769775390625 : Rat)/72507300583803020931143369083458597517524992,   box := { reLo := (12908149507470177171361434293207253006481299543081 : Rat)/38014707608480918237947294690028341175268143005696,            reHi := (283727490467678561020684408760984805789479016536927 : Rat)/76029415216961836475894589380056682350536286011392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_b3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := 4 }
def label : String := "378.c1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := 4 },   conductor := 378,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, -1, 0, 1, -1, 0, -1, -1, 0, 1, -5, 0, 0, 1, 0, 1, -2, 0, -1, -1, 0, 5, 1, 0, -4, 0, 0, -1, -4, 0,                    -9, -1, 0, 2, 1, 0, 5, 1, 0, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   finite := ((9136940158956903 : Rat)/9007199254740992, (7262070408529613 : Rat)/2251799813685248),   tail := (42723341893935745735584732530307769775390625 : Rat)/72507300583803020931143369083458597517524992,   box := { reLo := (32325882145041421648098335574295175966795299960503 : Rat)/76029415216961836475894589380056682350536286011392,            reHi := (72498518890791283228515119478343103088578007185213 : Rat)/19007353804240459118973647345014170587634071502848,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1062, a6 := 13590 }
def label : String := "378.d1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1062, a6 := 13590 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 1, -1, 0, 0, 0, 0, 5, -1, 0, 1, -3, 0, 2, 0, 0, 0, 9, 0, -5, -5, 0, 1, 3, 0, 5,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/121259495796231308852887305105441491849603586066053345354709477945025753963785163232363770828246829562320413932267640772779963243722866497809255918615872898274961178593276442354996414821045796810271651925620275987384207051569252000582340730848828386287688498794333053914148036937565425350696324612138255334409107530816348176974844331203663839539552857354758277171936435768939792910466665461465721652282402357154887345411247718546721827366503362864970096085184027734993048135907649885851466348367659095068130210718091404990480384,   box := { reLo := (1062643726036518586804079972236240257218466246865308294077415298466252439303290041972491527502665054554699155767231360630565823929981940657841519649036666992444624497270031747312262598190756265493046968652271197134150310581145729401458546964961777640645721986498916937485473341166032400107769641498804414264622139224323019001223490869879688028768125685315527436854791716607073764860248545716390885123155579080009178035999633536085226463319602852417952006144918198333754648948532588677546402407658498164228003113205487999277586885144099 : Rat)/1232383901378779056977119994811097442758431917888583029242256592703496017555971552037343313862784036973627019274352825363713458538788018176202540705797246360383594075473294172560087788127178536913168801492204360813603236185473364086058442404059158411377104312504071721874999758263680243097070132816460455923389969611655055710489853032667420315689185902103592548762438524324710058608690262084641114967868250224224765294446865756895450542282110144952449755682461884756142671849615947781636193534398451076700945616919052976742225286266880,            reHi := (320792219890690678924125342205573166510937999084573449045554497155320508977374909606769619870283722465787110247172833949406581259930824985211621955706454394256513582680491815233014386520697086173409090127487287632942849774537527284993538732058722165765926758679777637518873713473770557896079003031974041315301373130663133229994881423819920961748808828611076343035996383898037867262297069116688462371919872029212424872076781880129176576209218383364602986594641355332403023972652485803049755633503244977479001903866112746403535783455225 : Rat)/246476780275755811395423998962219488551686383577716605848451318540699203511194310407468662772556807394725403854870565072742691707757603635240508141159449272076718815094658834512017557625435707382633760298440872162720647237094672817211688480811831682275420862500814344374999951652736048619414026563292091184677993922331011142097970606533484063137837180420718509752487704864942011721738052416928222993573650044844953058889373151379090108456422028990489951136492376951228534369923189556327238706879690215340189123383810595348445057253376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/242518991592462617705774610210882983699207172132106690709418955890051507927570326464727541656493659124640827864535281545559926487445732995618511837231745796549922357186552884709992829642091593620543303851240551974768414103138504001164681461697656772575376997588666107828296073875130850701392649224276510668818215061632696353949688662407327679079105714709516554343872871537879585820933330922931443304564804714309774690822495437093443654733006725729940192170368055469986096271815299771702932696735318190136260421436182809980960768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := -12, a6 := 24 }
def label : String := "378.d2"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -12, a6 := 24 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 1, -1, 0, 0, 0, 0, 5, -1, 0, 1, -3, 0, 2, 0, 0, 0, 9, 0, -5, -5, 0, 1, 3, 0, 5,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/121259495796231308852887305105441491849603586066053345354709477945025753963785163232363770828246829562320413932267640772779963243722866497809255918615872898274961178593276442354996414821045796810271651925620275987384207051569252000582340730848828386287688498794333053914148036937565425350696324612138255334409107530816348176974844331203663839539552857354758277171936435768939792910466665461465721652282402357154887345411247718546721827366503362864970096085184027734993048135907649885851466348367659095068130210718091404990480384,   box := { reLo := (1062643726036518586804079972236240257218466246865308294077415298466252439303290041972491527502665054554699155767231360630565823929981940657841519649036666992444624497270031747312262598190756265493046968652271197134150310581145729401458546964961777640645721986498916937485473341166032400107769641498804414264622139224323019001223490869879688028768125685315527436854791716607073764860248545716390885123155579080009178035999633536085226463319602852417952006144918198333754648948532588677546402407658498164228003113205487999277586885144099 : Rat)/1232383901378779056977119994811097442758431917888583029242256592703496017555971552037343313862784036973627019274352825363713458538788018176202540705797246360383594075473294172560087788127178536913168801492204360813603236185473364086058442404059158411377104312504071721874999758263680243097070132816460455923389969611655055710489853032667420315689185902103592548762438524324710058608690262084641114967868250224224765294446865756895450542282110144952449755682461884756142671849615947781636193534398451076700945616919052976742225286266880,            reHi := (320792219890690678924125342205573166510937999084573449045554497155320508977374909606769619870283722465787110247172833949406581259930824985211621955706454394256513582680491815233014386520697086173409090127487287632942849774537527284993538732058722165765926758679777637518873713473770557896079003031974041315301373130663133229994881423819920961748808828611076343035996383898037867262297069116688462371919872029212424872076781880129176576209218383364602986594641355332403023972652485803049755633503244977479001903866112746403535783455225 : Rat)/246476780275755811395423998962219488551686383577716605848451318540699203511194310407468662772556807394725403854870565072742691707757603635240508141159449272076718815094658834512017557625435707382633760298440872162720647237094672817211688480811831682275420862500814344374999951652736048619414026563292091184677993922331011142097970606533484063137837180420718509752487704864942011721738052416928222993573650044844953058889373151379090108456422028990489951136492376951228534369923189556327238706879690215340189123383810595348445057253376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/242518991592462617705774610210882983699207172132106690709418955890051507927570326464727541656493659124640827864535281545559926487445732995618511837231745796549922357186552884709992829642091593620543303851240551974768414103138504001164681461697656772575376997588666107828296073875130850701392649224276510668818215061632696353949688662407327679079105714709516554343872871537879585820933330922931443304564804714309774690822495437093443654733006725729940192170368055469986096271815299771702932696735318190136260421436182809980960768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 0, a4 := 93, a6 := -235 }
def label : String := "378.d3"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 93, a6 := -235 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 32,   coefficients := [1, -1, 0, 1, 0, 0, 1, -1, 0, 0, 0, 0, 5, -1, 0, 1, -3, 0, 2, 0, 0, 0, 9, 0, -5, -5, 0, 1, 3, 0, 5,                    -1],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/121259495796231308852887305105441491849603586066053345354709477945025753963785163232363770828246829562320413932267640772779963243722866497809255918615872898274961178593276442354996414821045796810271651925620275987384207051569252000582340730848828386287688498794333053914148036937565425350696324612138255334409107530816348176974844331203663839539552857354758277171936435768939792910466665461465721652282402357154887345411247718546721827366503362864970096085184027734993048135907649885851466348367659095068130210718091404990480384,   box := { reLo := (1062643726036518586804079972236240257218466246865308294077415298466252439303290041972491527502665054554699155767231360630565823929981940657841519649036666992444624497270031747312262598190756265493046968652271197134150310581145729401458546964961777640645721986498916937485473341166032400107769641498804414264622139224323019001223490869879688028768125685315527436854791716607073764860248545716390885123155579080009178035999633536085226463319602852417952006144918198333754648948532588677546402407658498164228003113205487999277586885144099 : Rat)/1232383901378779056977119994811097442758431917888583029242256592703496017555971552037343313862784036973627019274352825363713458538788018176202540705797246360383594075473294172560087788127178536913168801492204360813603236185473364086058442404059158411377104312504071721874999758263680243097070132816460455923389969611655055710489853032667420315689185902103592548762438524324710058608690262084641114967868250224224765294446865756895450542282110144952449755682461884756142671849615947781636193534398451076700945616919052976742225286266880,            reHi := (320792219890690678924125342205573166510937999084573449045554497155320508977374909606769619870283722465787110247172833949406581259930824985211621955706454394256513582680491815233014386520697086173409090127487287632942849774537527284993538732058722165765926758679777637518873713473770557896079003031974041315301373130663133229994881423819920961748808828611076343035996383898037867262297069116688462371919872029212424872076781880129176576209218383364602986594641355332403023972652485803049755633503244977479001903866112746403535783455225 : Rat)/246476780275755811395423998962219488551686383577716605848451318540699203511194310407468662772556807394725403854870565072742691707757603635240508141159449272076718815094658834512017557625435707382633760298440872162720647237094672817211688480811831682275420862500814344374999951652736048619414026563292091184677993922331011142097970606533484063137837180420718509752487704864942011721738052416928222993573650044844953058889373151379090108456422028990489951136492376951228534369923189556327238706879690215340189123383810595348445057253376,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (26631259826114397994953093775437367628392162975362090009645784994712768335218099719530317678012781150019795592381673990909175187581187043200846920709131565112816119661262984618422478943934005324718716888408420249638649569669696711352282113239752008159990319079802309038934416680565343007636491983196744706369005005377935557559339752139645922760839556976647670378605937796010775146034133953678211725678169161390777777066717514155932440555322895192670073655933161554199170836069362866620916521227691224792157810255623204081578503 : Rat)/242518991592462617705774610210882983699207172132106690709418955890051507927570326464727541656493659124640827864535281545559926487445732995618511837231745796549922357186552884709992829642091593620543303851240551974768414103138504001164681461697656772575376997588666107828296073875130850701392649224276510668818215061632696353949688662407327679079105714709516554343872871537879585820933330922931443304564804714309774690822495437093443654733006725729940192170368055469986096271815299771702932696735318190136260421436182809980960768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 32 = (List.range 32).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 32

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_d3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -9560, a6 := -357371 }
def label : String := "378.e1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 2,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -9560, a6 := -357371 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 5, 1, 0, 1, 3, 0, 2, 0, 0, 0, -9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (13044905403200455434889670294865035113811602957617526630211558967334527517812215824441886086490365153203379174997092070746312901076513781781455745120208811805158310710103260589186612950954648972014671401860439204825957223808024965419998997106205492070262078475216151493640607450578434322711812081045052784312219346938315150800886892006702868252701882830338224792625159372350583912707991466591243874682157775 : Rat)/33588857329983634759693825738974879931666572445293700502744750939640438507779037031397442861262553939891673191631002752175422395637083632627972537960236371020542146113218893762503275369973735574707914408236244624011307266192463128283112286246358989519369830648325464451438421307612912663958218186409753901912847435051009388441459157932415418125252765430089991539020869765343809618795745451821340365414203392,            reHi := (132914398562112682867022192134012460025031574013184775666823648224888208960119236529795869999783763116144511341195620566782327202401438217939228385513311452361552866111079024974976783414461104218148634924853152051928650082305256306169305425196372420795345010240870814462107219832933055368220348586476024409526094656993890553198394083833222448671647649433296552225855169112404044357570724427680874628012164401 : Rat)/33588857329983634759693825738974879931666572445293700502744750939640438507779037031397442861262553939891673191631002752175422395637083632627972537960236371020542146113218893762503275369973735574707914408236244624011307266192463128283112286246358989519369830648325464451438421307612912663958218186409753901912847435051009388441459157932415418125252765430089991539020869765343809618795745451821340365414203392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -110, a6 := -539 }
def label : String := "378.e2"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -110, a6 := -539 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 5, 1, 0, 1, 3, 0, 2, 0, 0, 0, -9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (13044905403200455434889670294865035113811602957617526630211558967334527517812215824441886086490365153203379174997092070746312901076513781781455745120208811805158310710103260589186612950954648972014671401860439204825957223808024965419998997106205492070262078475216151493640607450578434322711812081045052784312219346938315150800886892006702868252701882830338224792625159372350583912707991466591243874682157775 : Rat)/33588857329983634759693825738974879931666572445293700502744750939640438507779037031397442861262553939891673191631002752175422395637083632627972537960236371020542146113218893762503275369973735574707914408236244624011307266192463128283112286246358989519369830648325464451438421307612912663958218186409753901912847435051009388441459157932415418125252765430089991539020869765343809618795745451821340365414203392,            reHi := (132914398562112682867022192134012460025031574013184775666823648224888208960119236529795869999783763116144511341195620566782327202401438217939228385513311452361552866111079024974976783414461104218148634924853152051928650082305256306169305425196372420795345010240870814462107219832933055368220348586476024409526094656993890553198394083833222448671647649433296552225855169112404044357570724427680874628012164401 : Rat)/33588857329983634759693825738974879931666572445293700502744750939640438507779037031397442861262553939891673191631002752175422395637083632627972537960236371020542146113218893762503275369973735574707914408236244624011307266192463128283112286246358989519369830648325464451438421307612912663958218186409753901912847435051009388441459157932415418125252765430089991539020869765343809618795745451821340365414203392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 10, a6 := 5 }
def label : String := "378.e3"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 10, a6 := 5 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 5, 1, 0, 1, 3, 0, 2, 0, 0, 0, -9, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (13044905403200455434889670294865035113811602957617526630211558967334527517812215824441886086490365153203379174997092070746312901076513781781455745120208811805158310710103260589186612950954648972014671401860439204825957223808024965419998997106205492070262078475216151493640607450578434322711812081045052784312219346938315150800886892006702868252701882830338224792625159372350583912707991466591243874682157775 : Rat)/33588857329983634759693825738974879931666572445293700502744750939640438507779037031397442861262553939891673191631002752175422395637083632627972537960236371020542146113218893762503275369973735574707914408236244624011307266192463128283112286246358989519369830648325464451438421307612912663958218186409753901912847435051009388441459157932415418125252765430089991539020869765343809618795745451821340365414203392,            reHi := (132914398562112682867022192134012460025031574013184775666823648224888208960119236529795869999783763116144511341195620566782327202401438217939228385513311452361552866111079024974976783414461104218148634924853152051928650082305256306169305425196372420795345010240870814462107219832933055368220348586476024409526094656993890553198394083833222448671647649433296552225855169112404044357570724427680874628012164401 : Rat)/33588857329983634759693825738974879931666572445293700502744750939640438507779037031397442861262553939891673191631002752175422395637083632627972537960236371020542146113218893762503275369973735574707914408236244624011307266192463128283112286246358989519369830648325464451438421307612912663958218186409753901912847435051009388441459157932415418125252765430089991539020869765343809618795745451821340365414203392,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_e3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := -107 }
def label : String := "378.f1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -2, a6 := -107 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 1, 0, -1, 1, 0, 1, 5, 0, 0, -1, 0, 1, 2, 0, -1, 1, 0, 5, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (60736481255616893951490235384426955560400291547202484152023747034019371028345506448469604796744552963093585583594092238002604698370498275238969680897076275795840944142107104212502690634402036780646859338651203250290235039795090721501012020519502800621751452558171240151099310065335773176412420540562330530876687485802113425170761686167905839051355652504425868898356348863489212239090375091081229532872041757 : Rat)/142106704088392300906396955049509107403204729576242579050073946283094162917526695132835335182264651284157078887669627028434479366156892291887576122139461569702293695094387627456744626565273496662225791727153342640047838433891190158120859672580749571043487745050607734217624090147593092039823230788656651123477431455985039720329250283560219076683761699896534579588165218237993040694905076911551824622906245120,            reHi := (51625149510931414036521290749061650565954043307692687776248532629702058696239549581654979495549605437185238964361883791724931300881127289386065545466928494047630803333880677239516995262581050536786151780151303444016757790837607559868290422649908152790503441488735249909557403287105038119484098018854209177454910669367821780266783200080974970825027027183846458398331278910323284750031502595184760383870885769 : Rat)/12918791280762936446036086822682646127564066325112961731824904207554014810684245012075939562024059207650643535242693366221316306014262935626143283830860142700208517735853420677885875142297590605656890157013940240004348948535562741647350879325522688276680704095509794019784008195235735639983930071696059193043402859635003610939022753050929006971251063626957689053469565294363003699536825173777438602082385920,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_f1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1271, a6 := -17117 }
def label : String := "378.g1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1271, a6 := -17117 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 3, 0, 1, 1, 0, 3, -3, 0, -4, 1, 0, 1, 6, 0, -7, 3, 0, -3, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (103196822102489332448356473189799950359091090953458183060808246413690002540253966445418555097569562952644623968009839572490152626988570190083615338249419803563500716061132407184843224039031122006654405227967400766533372607582573653148969668190299582282237103113474314896425909197692004013509630784582862239194405027375419784998417071271743795082592569473033674444664668469402272885957910386768013793191470603 : Rat)/167944286649918173798469128694874399658332862226468502513723754698202192538895185156987214306312769699458365958155013760877111978185418163139862689801181855102710730566094468812516376849868677873539572041181223120056536330962315641415561431231794947596849153241627322257192106538064563319791090932048769509564237175255046942207295789662077090626263827150449957695104348826719048093978727259106701827071016960,            reHi := (7727987166867555805995031783597070494483137464897198370776232787179455743411020262947483880613291751795951906929041232787672039658987389202369044903033070456241573794283565269981467338393896454334420964827953718596586319383933782844465645435731696240269429699272945876607733001259359016705341276606858531504936937750779622559352221180783920523395055776841301378902741797424103669331187876847750719483537874311 : Rat)/1847387153149099911783160415643618396241661484491153527650961301680224117927847036726859357369440466694042025539705151369648231760039599794538489587813000406129818036227039156937680145348555456608935292452993454320621899640585472055571175743549744423565340685657900544829113171918710196517702000252536464605206608927805516364280253686282847996888902098654949534646147837093909529033765999850173720097781186560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11, a6 := -37 }
def label : String := "378.g2"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -11, a6 := -37 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 3, 0, 1, 1, 0, 3, -3, 0, -4, 1, 0, 1, 6, 0, -7, 3, 0, -3, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (103196822102489332448356473189799950359091090953458183060808246413690002540253966445418555097569562952644623968009839572490152626988570190083615338249419803563500716061132407184843224039031122006654405227967400766533372607582573653148969668190299582282237103113474314896425909197692004013509630784582862239194405027375419784998417071271743795082592569473033674444664668469402272885957910386768013793191470603 : Rat)/167944286649918173798469128694874399658332862226468502513723754698202192538895185156987214306312769699458365958155013760877111978185418163139862689801181855102710730566094468812516376849868677873539572041181223120056536330962315641415561431231794947596849153241627322257192106538064563319791090932048769509564237175255046942207295789662077090626263827150449957695104348826719048093978727259106701827071016960,            reHi := (7727987166867555805995031783597070494483137464897198370776232787179455743411020262947483880613291751795951906929041232787672039658987389202369044903033070456241573794283565269981467338393896454334420964827953718596586319383933782844465645435731696240269429699272945876607733001259359016705341276606858531504936937750779622559352221180783920523395055776841301378902741797424103669331187876847750719483537874311 : Rat)/1847387153149099911783160415643618396241661484491153527650961301680224117927847036726859357369440466694042025539705151369648231760039599794538489587813000406129818036227039156937680145348555456608935292452993454320621899640585472055571175743549744423565340685657900544829113171918710196517702000252536464605206608927805516364280253686282847996888902098654949534646147837093909529033765999850173720097781186560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 94, a6 := 929 }
def label : String := "378.g3"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 94, a6 := 929 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 3, 0, 1, 1, 0, 3, -3, 0, -4, 1, 0, 1, 6, 0, -7, 3, 0, -3, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (103196822102489332448356473189799950359091090953458183060808246413690002540253966445418555097569562952644623968009839572490152626988570190083615338249419803563500716061132407184843224039031122006654405227967400766533372607582573653148969668190299582282237103113474314896425909197692004013509630784582862239194405027375419784998417071271743795082592569473033674444664668469402272885957910386768013793191470603 : Rat)/167944286649918173798469128694874399658332862226468502513723754698202192538895185156987214306312769699458365958155013760877111978185418163139862689801181855102710730566094468812516376849868677873539572041181223120056536330962315641415561431231794947596849153241627322257192106538064563319791090932048769509564237175255046942207295789662077090626263827150449957695104348826719048093978727259106701827071016960,            reHi := (7727987166867555805995031783597070494483137464897198370776232787179455743411020262947483880613291751795951906929041232787672039658987389202369044903033070456241573794283565269981467338393896454334420964827953718596586319383933782844465645435731696240269429699272945876607733001259359016705341276606858531504936937750779622559352221180783920523395055776841301378902741797424103669331187876847750719483537874311 : Rat)/1847387153149099911783160415643618396241661484491153527650961301680224117927847036726859357369440466694042025539705151369648231760039599794538489587813000406129818036227039156937680145348555456608935292452993454320621899640585472055571175743549744423565340685657900544829113171918710196517702000252536464605206608927805516364280253686282847996888902098654949534646147837093909529033765999850173720097781186560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_g3

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 1, a2 := -1, a3 := 1, a4 := 3967, a6 := 38449 }
def label : String := "378.h1"
def inputConductor : Nat := 378
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.globally_minimal
def localData : WildData := { atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -2 } }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 378 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.root_formula
def result : CentralResult := { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 3967, a6 := 38449 },   conductor := 378,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 1, 0, 1, 4, 0, -1, 1, 0, 4, -4, 0, 3, -1, 0, 1, -7, 0, 2, 4, 0, -4, -1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/16700741612110775470733642578125,   alphaHi := (1349303770452201895863057907712 : Rat)/4175185403027693843841552734375,   geometricUpper := (6519854073499239 : Rat)/9007199254740992,   tail := (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/49684792341837726462073675836711905573001812684318065234024591687225793937596850228163527342745838538740624714892192243606393115836636100325532310946907458032069371904903258188511721024931602429309425060146300175006630188779734790867261040038161984026616557104435490336265246986657445301170817343984228575441427839297746710532172194107759194551279978566458431449991597770755547562782244000451660873728,   box := { reLo := (108462067694476969761976392603185409385242258770012970274384714313586572628600398769177668119290986414630249797778991152366153168643006998854442972368473661392886318359770063892093180869345383658240967397295481405255900311950210684286835502485076985002567102050659173793406561396880218596639021356570212787699986266377393545694800879563759509070285083131032965236990899494410994946880002126091409750638929419 : Rat)/167944286649918173798469128694874399658332862226468502513723754698202192538895185156987214306312769699458365958155013760877111978185418163139862689801181855102710730566094468812516376849868677873539572041181223120056536330962315641415561431231794947596849153241627322257192106538064563319791090932048769509564237175255046942207295789662077090626263827150449957695104348826719048093978727259106701827071016960,            reHi := (7785904868379419864910124224357607803602209378698373375187275718929749665833582236299712617317645478341720904144117516067489658065640820830562367683998204255231006276480791474142165573751201537731857373846761976254185595580797556070540057103907884508689231392037167816895597520598811267785824565904158332403134870909480718963324390472427601994944057014687074782184369662610993305311588170381355448826888543623 : Rat)/1847387153149099911783160415643618396241661484491153527650961301680224117927847036726859357369440466694042025539705151369648231760039599794538489587813000406129818036227039156937680145348555456608935292452993454320621899640585472055571175743549744423565340685657900544829113171918710196517702000252536464605206608927805516364280253686282847996888902098654949534646147837093909529033765999850173720097781186560,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (88655752966110087956803854847889199724994037757286880938507556046694056954753070016981087139064258219409992422013225874295798063339861523198795291070863019827027929831685922829818304553799429608983536063610852810178166209174235536699072090175580123222067173860526763964248701188113811668757078475511429871401639668083814524805853899016512544291080966084818306633371581486625369489863554088828515234375 : Rat)/99369584683675452924147351673423811146003625368636130468049183374451587875193700456327054685491677077481249429784384487212786231673272200651064621893814916064138743809806516377023442049863204858618850120292600350013260377559469581734522080076323968053233114208870980672530493973314890602341634687968457150882855678595493421064344388215518389102559957132916862899983195541511095125564488000903321747456, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N378.C378_h1
