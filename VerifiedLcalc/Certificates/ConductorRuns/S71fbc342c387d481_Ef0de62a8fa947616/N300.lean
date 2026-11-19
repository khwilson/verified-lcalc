module
public import VerifiedLcalc.Assumptions.DerivativeCertification
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option pp.fullNames true

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := 22 }
def label : String := "300.a1"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := 22 },   conductor := 300,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -4, 0, 1, 0, -4, 0, 0, 0, 0, 0, -4, 0, 0, 0, 4, 0, -4, 0, 0, 0, -1, 0, -6, 0, 4,                    0, 4, 0, 0, 0, 8, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   finite := ((11091377855864199 : Rat)/9007199254740992, (25441883338216129 : Rat)/9007199254740992),   tail := (101010492031405585246444653046131134033203125 : Rat)/370634609052256409191072991428797833729277952,   box := { reLo := (745297145776633181301292824767565935854022670784863 : Rat)/777277111643157633047877106120886234601022715592704,            reHi := (2407344084502930868006420809991783585467358533471273 : Rat)/777277111643157633047877106120886234601022715592704,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := 12, a6 := 72 }
def label : String := "300.a2"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.conductor_formula
theorem root_formula : wildSign equation localData = -1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.root_formula
theorem rank_lower_bound : 1 ≤ analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) := rank_lower_bound_of_wild_negative equation nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.rank_lower_bound
def result : DerivativeResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 12, a6 := 72 },   conductor := 300,   policy := { precisionBits := 53 },   termLimit := 40,   stepsPerUnit := 1,   cutoff := 16,   coefficients := [1, 0, -1, 0, 0, 0, -4, 0, 1, 0, -4, 0, 0, 0, 0, 0, -4, 0, 0, 0, 4, 0, -4, 0, 0, 0, -1, 0, -6, 0, 4,                    0, 4, 0, 0, 0, 8, 0, 0, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   finite := ((11091377855864199 : Rat)/9007199254740992, (25441883338216129 : Rat)/9007199254740992),   tail := (101010492031405585246444653046131134033203125 : Rat)/370634609052256409191072991428797833729277952,   box := { reLo := (745297145776633181301292824767565935854022670784863 : Rat)/777277111643157633047877106120886234601022715592704,            reHi := (2407344084502930868006420809991783585467358533471273 : Rat)/777277111643157633047877106120886234601022715592704,            imLo := 0,            imHi := 0 } }
theorem payload_correct : DerivativePayloadCorrect result := by
  have h := VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a1.payload_correct
  exact ⟨h.1,h.2.1,h.2.2.1,by decide +kernel,h.2.2.2.2⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 1 := certifyDerivativeModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 40 = (List.range 40).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 40

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_a2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1213, a6 := -15863 }
def label : String := "300.b1"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -1213, a6 := -15863 },   conductor := 300,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 6, 0, -5, 0, 0, 0, 6, 0, 5, 0, -1, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   geometricUpper := (6266790251263067 : Rat)/9007199254740992,   tail := (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/56639858222554592512338110513859204567685598072116465228964880245139540864662298324478512104477504999179044107672705911469864195858787513878019067230943763401485054595566808292168221521986560595668931894264950013583694126908485640458963351482803724714934490656121220648611294934400870948856900052202830192070604205293454955281763970367473402695113533706673221365282889432773407754275649720524822544384,   box := { reLo := (34699670176624206272465300040769735056860139512798020114392855290534522858416531555161545698420349894558569087731796348259334917920474526607522113652144754403574479488041372652961592018440560960328804836823829772654968973229226693911018694183699962050435759498679832616734408819957790975963147129487401820621696490169607713330127935946517417380163907943376562565413857596064654625358157323893080788578504405 : Rat)/54938906640273055544600084717017498795313431876412735661673835926497755312955624843496097907467941046548698234075186880242512704192952266048748276622931291242775056921007341472346117661459782194420398200548279299725762208583296908190340223074423646058020292967227244271312849136225878393391778486735126998572531890404287209519697316573367808938776579175928117854462078980217789546006997683767741598553604096,            reHi := (98625572051552469414014213555677163744307499941501042581061692660737811491747515571098365254676371003091260325937603533052041958373359127045456157317520702346755269282138866784619283231783699814758006257788471674272759840405176536658683888431793549571859762834282038297432112818241140101436529230325743870155763949146751803427037374032842818943066164572030761362444927174451786513804387291416343420193567019 : Rat)/54938906640273055544600084717017498795313431876412735661673835926497755312955624843496097907467941046548698234075186880242512704192952266048748276622931291242775056921007341472346117661459782194420398200548279299725762208583296908190340223074423646058020292967227244271312849136225878393391778486735126998572531890404287209519697316573367808938776579175928117854462078980217789546006997683767741598553604096,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/113279716445109185024676221027718409135371196144232930457929760490279081729324596648957024208955009998358088215345411822939728391717575027756038134461887526802970109191133616584336443043973121191337863788529900027167388253816971280917926702965607449429868981312242441297222589868801741897713800104405660384141208410586909910563527940734946805390227067413346442730565778865546815508551299441049645088768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := -23 }
def label : String := "300.b2"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -13, a6 := -23 },   conductor := 300,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 6, 0, -5, 0, 0, 0, 6, 0, 5, 0, -1, 0, 6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   geometricUpper := (6266790251263067 : Rat)/9007199254740992,   tail := (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/56639858222554592512338110513859204567685598072116465228964880245139540864662298324478512104477504999179044107672705911469864195858787513878019067230943763401485054595566808292168221521986560595668931894264950013583694126908485640458963351482803724714934490656121220648611294934400870948856900052202830192070604205293454955281763970367473402695113533706673221365282889432773407754275649720524822544384,   box := { reLo := (34699670176624206272465300040769735056860139512798020114392855290534522858416531555161545698420349894558569087731796348259334917920474526607522113652144754403574479488041372652961592018440560960328804836823829772654968973229226693911018694183699962050435759498679832616734408819957790975963147129487401820621696490169607713330127935946517417380163907943376562565413857596064654625358157323893080788578504405 : Rat)/54938906640273055544600084717017498795313431876412735661673835926497755312955624843496097907467941046548698234075186880242512704192952266048748276622931291242775056921007341472346117661459782194420398200548279299725762208583296908190340223074423646058020292967227244271312849136225878393391778486735126998572531890404287209519697316573367808938776579175928117854462078980217789546006997683767741598553604096,            reHi := (98625572051552469414014213555677163744307499941501042581061692660737811491747515571098365254676371003091260325937603533052041958373359127045456157317520702346755269282138866784619283231783699814758006257788471674272759840405176536658683888431793549571859762834282038297432112818241140101436529230325743870155763949146751803427037374032842818943066164572030761362444927174451786513804387291416343420193567019 : Rat)/54938906640273055544600084717017498795313431876412735661673835926497755312955624843496097907467941046548698234075186880242512704192952266048748276622931291242775056921007341472346117661459782194420398200548279299725762208583296908190340223074423646058020292967227244271312849136225878393391778486735126998572531890404287209519697316573367808938776579175928117854462078980217789546006997683767741598553604096,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/113279716445109185024676221027718409135371196144232930457929760490279081729324596648957024208955009998358088215345411822939728391717575027756038134461887526802970109191133616584336443043973121191337863788529900027167388253816971280917926702965607449429868981312242441297222589868801741897713800104405660384141208410586909910563527940734946805390227067413346442730565778865546815508551299441049645088768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_b2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -30333, a6 := -2043537 }
def label : String := "300.c1"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -30333, a6 := -2043537 },   conductor := 300,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 6, 0, 5, 0, 0, 0, -6, 0, 5, 0, -1, 0, -6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   geometricUpper := (6266790251263067 : Rat)/9007199254740992,   tail := (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/56639858222554592512338110513859204567685598072116465228964880245139540864662298324478512104477504999179044107672705911469864195858787513878019067230943763401485054595566808292168221521986560595668931894264950013583694126908485640458963351482803724714934490656121220648611294934400870948856900052202830192070604205293454955281763970367473402695113533706673221365282889432773407754275649720524822544384,   box := { reLo := (8210467214767865993879007614760522283110220324527382937550156627119517412392890537817734052533907830151018440550882712976908963329853984369996186393908677367478052080027682596579225062916704194247538248426888565268830018040972241340308753008493314700856902614269828531576889589228228109418287741053869146927964707919422204551117190289995399356291726761703076921889943046082347364091099893404574314064235331 : Rat)/7848415234324722220657154959573928399330490268058962237381976560928250758993660691928013986781134435221242604867883840034644672027564609435535468088990184463253579560143905924620873951637111742060056885792611328532251744083328129741477174724917663722574327566746749181616121305175125484770254069533589571224647412914898172788528188081909686991253797025132588264923154140031112792286713954823963085507657728,            reHi := (121399172378303325098701966818231084669218902700394703029519933760039910520081217780660957923993375919589820322061986175631069783761862491027907348422736689515527154354291272307712266653760068214161969159952861858499600993462755532129826465307546790427422321635491005401735931122880945891401396288215426078029820414413099521954729770116293197056944343960575737250260670900963563437083929221355282830064709931 : Rat)/54938906640273055544600084717017498795313431876412735661673835926497755312955624843496097907467941046548698234075186880242512704192952266048748276622931291242775056921007341472346117661459782194420398200548279299725762208583296908190340223074423646058020292967227244271312849136225878393391778486735126998572531890404287209519697316573367808938776579175928117854462078980217789546006997683767741598553604096,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/113279716445109185024676221027718409135371196144232930457929760490279081729324596648957024208955009998358088215345411822939728391717575027756038134461887526802970109191133616584336443043973121191337863788529900027167388253816971280917926702965607449429868981312242441297222589868801741897713800104405660384141208410586909910563527940734946805390227067413346442730565778865546815508551299441049645088768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -333, a6 := -3537 }
def label : String := "300.c2"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -333, a6 := -3537 },   conductor := 300,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 6, 0, 5, 0, 0, 0, -6, 0, 5, 0, -1, 0, -6, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   geometricUpper := (6266790251263067 : Rat)/9007199254740992,   tail := (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/56639858222554592512338110513859204567685598072116465228964880245139540864662298324478512104477504999179044107672705911469864195858787513878019067230943763401485054595566808292168221521986560595668931894264950013583694126908485640458963351482803724714934490656121220648611294934400870948856900052202830192070604205293454955281763970367473402695113533706673221365282889432773407754275649720524822544384,   box := { reLo := (8210467214767865993879007614760522283110220324527382937550156627119517412392890537817734052533907830151018440550882712976908963329853984369996186393908677367478052080027682596579225062916704194247538248426888565268830018040972241340308753008493314700856902614269828531576889589228228109418287741053869146927964707919422204551117190289995399356291726761703076921889943046082347364091099893404574314064235331 : Rat)/7848415234324722220657154959573928399330490268058962237381976560928250758993660691928013986781134435221242604867883840034644672027564609435535468088990184463253579560143905924620873951637111742060056885792611328532251744083328129741477174724917663722574327566746749181616121305175125484770254069533589571224647412914898172788528188081909686991253797025132588264923154140031112792286713954823963085507657728,            reHi := (121399172378303325098701966818231084669218902700394703029519933760039910520081217780660957923993375919589820322061986175631069783761862491027907348422736689515527154354291272307712266653760068214161969159952861858499600993462755532129826465307546790427422321635491005401735931122880945891401396288215426078029820414413099521954729770116293197056944343960575737250260670900963563437083929221355282830064709931 : Rat)/54938906640273055544600084717017498795313431876412735661673835926497755312955624843496097907467941046548698234075186880242512704192952266048748276622931291242775056921007341472346117661459782194420398200548279299725762208583296908190340223074423646058020292967227244271312849136225878393391778486735126998572531890404287209519697316573367808938776579175928117854462078980217789546006997683767741598553604096,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/113279716445109185024676221027718409135371196144232930457929760490279081729324596648957024208955009998358088215345411822939728391717575027756038134461887526802970109191133616584336443043973121191337863788529900027167388253816971280917926702965607449429868981312242441297222589868801741897713800104405660384141208410586909910563527940734946805390227067413346442730565778865546815508551299441049645088768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_c2

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := -333, a6 := 2088 }
def label : String := "300.d1"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.globally_minimal
def localData : WildData := { atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -333, a6 := 2088 },   conductor := 300,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 0, 0, 4, 0, 1, 0, -4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   geometricUpper := (6266790251263067 : Rat)/9007199254740992,   tail := (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/56639858222554592512338110513859204567685598072116465228964880245139540864662298324478512104477504999179044107672705911469864195858787513878019067230943763401485054595566808292168221521986560595668931894264950013583694126908485640458963351482803724714934490656121220648611294934400870948856900052202830192070604205293454955281763970367473402695113533706673221365282889432773407754275649720524822544384,   box := { reLo := (249279857354512228439709892161772565847824727850299738969718900206810408516390184509881258000157639699813137888835417155511191003546028406009440103075862176710551944833811278478004538116515768237773139293667459884432298813304151692496535590191047275243227265065023009299238719892379872859585597398032610078646439992683596069601592080576481967704977912519784695050823918832773784036714818592376360537343891 : Rat)/222424723239971884795951759987925096337301343629201358954145084722662976975528845520227117034283162131776106210830716114342156697137458566998980877015916158877631809396790856163344605916841223459191895548778458703343166836369623110082349081272970226955547744806588033487096555207392220216161046505000514164261262714187397609391487111633068052383710846866105740301465906802501172251040476452500978131795968,            reHi := (72584168098029368375315788778991472602781779286778667738997028776758576754533349978422213787271697264711979610348680268193167759709363259273742796703433487996683840208893125558755156658999444280351424175119517927191328368621217510429688229449309071167857601205968595611939841078621702654830408449191634752279883699860344744235336848078942542489005964271962055834387605690850491971989502109123226487013099 : Rat)/31774960462853126399421679998275013762471620518457336993449297817523282425075549360032445290611880304539443744404388016334593813876779795285568696716559451268233115628112979451906372273834460494170270792682636957620452405195660444297478440181852889565078249258084004783870936458198888602308720929285787737751608959169628229913069587376152578911958692409443677185923700971785881750148639493214425447399424,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/113279716445109185024676221027718409135371196144232930457929760490279081729324596648957024208955009998358088215345411822939728391717575027756038134461887526802970109191133616584336443043973121191337863788529900027167388253816971280917926702965607449429868981312242441297222589868801741897713800104405660384141208410586909910563527940734946805390227067413346442730565778865546815508551299441049645088768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d1

namespace VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions
def equation : Artifacts.CurveEquation := { a1 := 0, a2 := 1, a3 := 0, a4 := 292, a6 := 9588 }
def label : String := "300.d2"
def inputConductor : Nat := 300
theorem nonsingular : discriminant equation ≠ 0 := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.nonsingular
def minimality : MinimalityWitness := { primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5, 5] }
theorem minimality_valid : minimality.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.minimality_valid
theorem globally_minimal : GloballyMinimalInput equation := minimal_of_witness equation minimality minimality_valid

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.globally_minimal
def localData : WildData := { atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }
theorem local_data_valid : localData.Valid equation := by decide +kernel

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.local_data_valid
theorem conductor_formula : wildLevel equation localData = 300 := (wildLevel_eq_fast equation localData).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.conductor_formula
theorem root_formula : wildSign equation localData = 1 := (wildSign_eq_fast equation localData local_data_valid).trans (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.root_formula
def result : CentralResult := { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 292, a6 := 9588 },   conductor := 300,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 24,   coefficients := [1, 0, 1, 0, 0, 0, 4, 0, 1, 0, -4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/7439101573518717288970947265625,   alphaHi := (5397215081808807583452231630848 : Rat)/14878203147037434482574462890625,   geometricUpper := (6266790251263067 : Rat)/9007199254740992,   tail := (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/56639858222554592512338110513859204567685598072116465228964880245139540864662298324478512104477504999179044107672705911469864195858787513878019067230943763401485054595566808292168221521986560595668931894264950013583694126908485640458963351482803724714934490656121220648611294934400870948856900052202830192070604205293454955281763970367473402695113533706673221365282889432773407754275649720524822544384,   box := { reLo := (249279857354512228439709892161772565847824727850299738969718900206810408516390184509881258000157639699813137888835417155511191003546028406009440103075862176710551944833811278478004538116515768237773139293667459884432298813304151692496535590191047275243227265065023009299238719892379872859585597398032610078646439992683596069601592080576481967704977912519784695050823918832773784036714818592376360537343891 : Rat)/222424723239971884795951759987925096337301343629201358954145084722662976975528845520227117034283162131776106210830716114342156697137458566998980877015916158877631809396790856163344605916841223459191895548778458703343166836369623110082349081272970226955547744806588033487096555207392220216161046505000514164261262714187397609391487111633068052383710846866105740301465906802501172251040476452500978131795968,            reHi := (72584168098029368375315788778991472602781779286778667738997028776758576754533349978422213787271697264711979610348680268193167759709363259273742796703433487996683840208893125558755156658999444280351424175119517927191328368621217510429688229449309071167857601205968595611939841078621702654830408449191634752279883699860344744235336848078942542489005964271962055834387605690850491971989502109123226487013099 : Rat)/31774960462853126399421679998275013762471620518457336993449297817523282425075549360032445290611880304539443744404388016334593813876779795285568696716559451268233115628112979451906372273834460494170270792682636957620452405195660444297478440181852889565078249258084004783870936458198888602308720929285787737751608959169628229913069587376152578911958692409443677185923700971785881750148639493214425447399424,            imLo := 0,            imHi := 0 } }
theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, (32952548934516575832412579479721887294067259203430625375088445144324371916885824374838289724830220389800102426637632068097751866392837888011709098065190991769362167395523699265207792324771696108663870465514781838395292760640490112743031558763512023469310411560103490052060137867611910339613632040741441315314406671658355091546748410939617504479523795244067026500576870184862027947292133414733323046875 : Rat)/113279716445109185024676221027718409135371196144232930457929760490279081729324596648957024208955009998358088215345411822939728391717575027756038134461887526802970109191133616584336443043973121191337863788529900027167388253816971280917926702965607449429868981312242441297222589868801741897713800104405660384141208410586909910563527940734946805390227067413346442730565778865546815508551299441049645088768, by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.payload_correct
theorem analytic_rank : analyticOrderAt (modularWitness equation nonsingular).formL (1 : ℂ) = 0 := certifyWildCentralModel result nonsingular minimality minimality_valid localData local_data_valid (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.analytic_rank
theorem coefficients_correct : modelCoefficients equation 24 = (List.range 24).map (fun j => (weierstrass equation ℚ).LFunction (j+1)) := minimal_prefix equation nonsingular globally_minimal 24

#print axioms VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2.coefficients_correct
end VerifiedLcalc.Certificates.ConductorRuns.S71fbc342c387d481_Ef0de62a8fa947616.N300.C300_d2
