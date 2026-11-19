module
public import VerifiedLcalc.Assumptions.Batch
public import VerifiedLcalc.Assumptions.FastSign
public import VerifiedLcalc.Assumptions.TameCertification
public import VerifiedLcalc.Assumptions.WildCertification

@[expose] public section

namespace VerifiedLcalc.Certificates.Batch.C32_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := -14 },   conductor := 32,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4859200799961679553985595703125,   alphaHi := (1349303770452201895863057907712 : Rat)/1214800199990419864654541015625,   geometricUpper := (2966264568651001 : Rat)/9007199254740992,   tail := (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,   box := { reLo := (113106233477987953219754146542784828587829820186762283342676440168460110193256375 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            reHi := (400157478082033231972318505176881818810007313210195400198702706428184327620368457 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/779274473542914624433994093647101609108880903332460569173644561039454057837625344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C32_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C32_a1

namespace VerifiedLcalc.Certificates.Batch.C32_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -11, a6 := 14 },   conductor := 32,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4859200799961679553985595703125,   alphaHi := (1349303770452201895863057907712 : Rat)/1214800199990419864654541015625,   geometricUpper := (2966264568651001 : Rat)/9007199254740992,   tail := (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,   box := { reLo := (113106233477987953219754146542784828587829820186762283342676440168460110193256375 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            reHi := (400157478082033231972318505176881818810007313210195400198702706428184327620368457 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/779274473542914624433994093647101609108880903332460569173644561039454057837625344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C32_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C32_a2

namespace VerifiedLcalc.Certificates.Batch.C32_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -1, a6 := 0 },   conductor := 32,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4859200799961679553985595703125,   alphaHi := (1349303770452201895863057907712 : Rat)/1214800199990419864654541015625,   geometricUpper := (2966264568651001 : Rat)/9007199254740992,   tail := (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,   box := { reLo := (113106233477987953219754146542784828587829820186762283342676440168460110193256375 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            reHi := (400157478082033231972318505176881818810007313210195400198702706428184327620368457 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/779274473542914624433994093647101609108880903332460569173644561039454057837625344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C32_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C32_a3

namespace VerifiedLcalc.Certificates.Batch.C32_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 4, a6 := 0 },   conductor := 32,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4859200799961679553985595703125,   alphaHi := (1349303770452201895863057907712 : Rat)/1214800199990419864654541015625,   geometricUpper := (2966264568651001 : Rat)/9007199254740992,   tail := (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,   box := { reLo := (113106233477987953219754146542784828587829820186762283342676440168460110193256375 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            reHi := (400157478082033231972318505176881818810007313210195400198702706428184327620368457 : Rat)/389637236771457312216997046823550804554440451666230284586822280519727028918812672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (143525622302022596117859027817488393437658531453702238128378789212769283284375625 : Rat)/779274473542914624433994093647101609108880903332460569173644561039454057837625344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] }) (by decide +kernel)
    ({ atTwo := some { r := 0,              s := 0,              t := 0,              starT := 0,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 0],              kodaira := -7 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C32_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C32_a4

namespace VerifiedLcalc.Certificates.Batch.C33_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -146, a6 := 621 },   conductor := 33,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/4934541739340808200836181640625,   alphaHi := (42165742826631309245720559616 : Rat)/38551107338600063323974609375,   geometricUpper := (1508498558448505 : Rat)/4503599627370496,   tail := (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,   box := { reLo := (2470935292715602739664501666592491343365171730911257230299654194028364758206753 : Rat)/7192999326351334817817402702073474548209632097487736574665863329272996294557696,            reHi := (2776475402861724404423945290764107566839712285093679150380722032439628204358901 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/4795332884234223211878268468048983032139754731658491049777242219515330863038464, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C33_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C33_a1

namespace VerifiedLcalc.Certificates.Batch.C33_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -11, a6 := 0 },   conductor := 33,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/4934541739340808200836181640625,   alphaHi := (42165742826631309245720559616 : Rat)/38551107338600063323974609375,   geometricUpper := (1508498558448505 : Rat)/4503599627370496,   tail := (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,   box := { reLo := (2470935292715602739664501666592491343365171730911257230299654194028364758206753 : Rat)/7192999326351334817817402702073474548209632097487736574665863329272996294557696,            reHi := (2776475402861724404423945290764107566839712285093679150380722032439628204358901 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/4795332884234223211878268468048983032139754731658491049777242219515330863038464, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C33_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C33_a2

namespace VerifiedLcalc.Certificates.Batch.C33_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -6, a6 := -9 },   conductor := 33,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/4934541739340808200836181640625,   alphaHi := (42165742826631309245720559616 : Rat)/38551107338600063323974609375,   geometricUpper := (1508498558448505 : Rat)/4503599627370496,   tail := (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,   box := { reLo := (2470935292715602739664501666592491343365171730911257230299654194028364758206753 : Rat)/7192999326351334817817402702073474548209632097487736574665863329272996294557696,            reHi := (2776475402861724404423945290764107566839712285093679150380722032439628204358901 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/4795332884234223211878268468048983032139754731658491049777242219515330863038464, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C33_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C33_a3

namespace VerifiedLcalc.Certificates.Batch.C33_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 44, a6 := 55 },   conductor := 33,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/4934541739340808200836181640625,   alphaHi := (42165742826631309245720559616 : Rat)/38551107338600063323974609375,   geometricUpper := (1508498558448505 : Rat)/4503599627370496,   tail := (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,   box := { reLo := (2470935292715602739664501666592491343365171730911257230299654194028364758206753 : Rat)/7192999326351334817817402702073474548209632097487736574665863329272996294557696,            reHi := (2776475402861724404423945290764107566839712285093679150380722032439628204358901 : Rat)/2397666442117111605939134234024491516069877365829245524888621109757665431519232,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (976415152644927857696120407304666198064583770144645478111540415097401758203125 : Rat)/4795332884234223211878268468048983032139754731658491049777242219515330863038464, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C33_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C33_a4

namespace VerifiedLcalc.Certificates.Batch.C34_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -113, a6 := -329 },   conductor := 34,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/2504374769290979671478271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/5008749538581959247589111328125,   geometricUpper := (766571290840715 : Rat)/2251799813685248,   tail := (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,   box := { reLo := (66944414079822290651608372679819824372900195261612924455331114275567464471027 : Rat)/221359666390373870038589163872168329566558097926132485810996221783998839390208,            reHi := (88491147141822321396607634981366229438212621976712151189062523352069550509231 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/147573110926915913359059442581445553044372065284088323873997481189332559593472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C34_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C34_a1

namespace VerifiedLcalc.Certificates.Batch.C34_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -103, a6 := -411 },   conductor := 34,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/2504374769290979671478271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/5008749538581959247589111328125,   geometricUpper := (766571290840715 : Rat)/2251799813685248,   tail := (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,   box := { reLo := (66944414079822290651608372679819824372900195261612924455331114275567464471027 : Rat)/221359666390373870038589163872168329566558097926132485810996221783998839390208,            reHi := (88491147141822321396607634981366229438212621976712151189062523352069550509231 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/147573110926915913359059442581445553044372065284088323873997481189332559593472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C34_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C34_a2

namespace VerifiedLcalc.Certificates.Batch.C34_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -43, a6 := 105 },   conductor := 34,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/2504374769290979671478271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/5008749538581959247589111328125,   geometricUpper := (766571290840715 : Rat)/2251799813685248,   tail := (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,   box := { reLo := (66944414079822290651608372679819824372900195261612924455331114275567464471027 : Rat)/221359666390373870038589163872168329566558097926132485810996221783998839390208,            reHi := (88491147141822321396607634981366229438212621976712151189062523352069550509231 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/147573110926915913359059442581445553044372065284088323873997481189332559593472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C34_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C34_a3

namespace VerifiedLcalc.Certificates.Batch.C34_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -3, a6 := 1 },   conductor := 34,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -2, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/2504374769290979671478271484375,   alphaHi := (5397215081808807583452231630848 : Rat)/5008749538581959247589111328125,   geometricUpper := (766571290840715 : Rat)/2251799813685248,   tail := (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,   box := { reLo := (66944414079822290651608372679819824372900195261612924455331114275567464471027 : Rat)/221359666390373870038589163872168329566558097926132485810996221783998839390208,            reHi := (88491147141822321396607634981366229438212621976712151189062523352069550509231 : Rat)/73786555463457956679529721290722776522186032642044161936998740594666279796736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (33088171224274092459148666076940683634555211703999557679421240043730055859375 : Rat)/147573110926915913359059442581445553044372065284088323873997481189332559593472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C34_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C34_a4

namespace VerifiedLcalc.Certificates.Batch.C35_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -131, a6 := -650 },   conductor := 35,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (674651885226100947929381470208 : Rat)/635234229723490619659423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/5081873837787924861907958984375,   geometricUpper := (1557099561239059 : Rat)/4503599627370496,   tail := (5720868023142273435916832784647914138396785247309606859924657631951347699561875 : Rat)/11628452938465490362820046086617113091652739008153597603676759987557804778979328,   box := { reLo := (2474341376394234025605427806237126423696233189095586424234052376615864735484525 : Rat)/11628452938465490362820046086617113091652739008153597603676759987557804778979328,            reHi := (41748232268036367221652046930046339613223588344793842114831677998488577505140921 : Rat)/34885358815396471088460138259851339274958217024460792811030279962673414336937984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (5720868023142273435916832784647914138396785247309606859924657631951347699561875 : Rat)/23256905876930980725640092173234226183305478016307195207353519975115609557958656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C35_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C35_a1

namespace VerifiedLcalc.Certificates.Batch.C35_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1, a6 := 0 },   conductor := 35,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (674651885226100947929381470208 : Rat)/635234229723490619659423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/5081873837787924861907958984375,   geometricUpper := (1557099561239059 : Rat)/4503599627370496,   tail := (5720868023142273435916832784647914138396785247309606859924657631951347699561875 : Rat)/11628452938465490362820046086617113091652739008153597603676759987557804778979328,   box := { reLo := (2474341376394234025605427806237126423696233189095586424234052376615864735484525 : Rat)/11628452938465490362820046086617113091652739008153597603676759987557804778979328,            reHi := (41748232268036367221652046930046339613223588344793842114831677998488577505140921 : Rat)/34885358815396471088460138259851339274958217024460792811030279962673414336937984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (5720868023142273435916832784647914138396785247309606859924657631951347699561875 : Rat)/23256905876930980725640092173234226183305478016307195207353519975115609557958656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C35_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C35_a2

namespace VerifiedLcalc.Certificates.Batch.C35_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 9, a6 := 1 },   conductor := 35,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (674651885226100947929381470208 : Rat)/635234229723490619659423828125,   alphaHi := (5397215081808807583452231630848 : Rat)/5081873837787924861907958984375,   geometricUpper := (1557099561239059 : Rat)/4503599627370496,   tail := (5720868023142273435916832784647914138396785247309606859924657631951347699561875 : Rat)/11628452938465490362820046086617113091652739008153597603676759987557804778979328,   box := { reLo := (2474341376394234025605427806237126423696233189095586424234052376615864735484525 : Rat)/11628452938465490362820046086617113091652739008153597603676759987557804778979328,            reHi := (41748232268036367221652046930046339613223588344793842114831677998488577505140921 : Rat)/34885358815396471088460138259851339274958217024460792811030279962673414336937984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (5720868023142273435916832784647914138396785247309606859924657631951347699561875 : Rat)/23256905876930980725640092173234226183305478016307195207353519975115609557958656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C35_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C35_a3

namespace VerifiedLcalc.Certificates.Batch.C36_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -135, a6 := -594 },   conductor := 36,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5153960755200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/300000000000000000000,   geometricUpper := (3160804625691237 : Rat)/9007199254740992,   tail := (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,   box := { reLo := (60104114563231677028857223165462644563418914911559297783992063694315669028285115 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            reHi := (454469032837471507044507885823526186563983468898776246342876390955820051672388933 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/733177690279376681889009559482607538431452423842651337938833201550936921738313728, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C36_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C36_a1

namespace VerifiedLcalc.Certificates.Batch.C36_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -15, a6 := 22 },   conductor := 36,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5153960755200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/300000000000000000000,   geometricUpper := (3160804625691237 : Rat)/9007199254740992,   tail := (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,   box := { reLo := (60104114563231677028857223165462644563418914911559297783992063694315669028285115 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            reHi := (454469032837471507044507885823526186563983468898776246342876390955820051672388933 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/733177690279376681889009559482607538431452423842651337938833201550936921738313728, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C36_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C36_a2

namespace VerifiedLcalc.Certificates.Batch.C36_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := -27 },   conductor := 36,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5153960755200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/300000000000000000000,   geometricUpper := (3160804625691237 : Rat)/9007199254740992,   tail := (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,   box := { reLo := (60104114563231677028857223165462644563418914911559297783992063694315669028285115 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            reHi := (454469032837471507044507885823526186563983468898776246342876390955820051672388933 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/733177690279376681889009559482607538431452423842651337938833201550936921738313728, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 0,                s := 0,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C36_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C36_a3

namespace VerifiedLcalc.Certificates.Batch.C36_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 0, a6 := 1 },   conductor := 36,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5153960755200000095367431640625,   alphaHi := (314159265358979323847 : Rat)/300000000000000000000,   geometricUpper := (3160804625691237 : Rat)/9007199254740992,   tail := (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,   box := { reLo := (60104114563231677028857223165462644563418914911559297783992063694315669028285115 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            reHi := (454469032837471507044507885823526186563983468898776246342876390955820051672388933 : Rat)/366588845139688340944504779741303769215726211921325668969416600775468460869156864,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (197182459137119833608750042363450473725654952980663108901226291593044186224973125 : Rat)/733177690279376681889009559482607538431452423842651337938833201550936921738313728, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := some { r := 2,                s := 0,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 3 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C36_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C36_a4

namespace VerifiedLcalc.Certificates.Batch.C37_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -1873, a6 := -31833 },   conductor := 37,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   geometricUpper := (3206162929939955 : Rat)/9007199254740992,   tail := (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,   box := { reLo := (30283418204113213282209638897320898491570332611770748800561922881321558428265531 : Rat)/216728975881336305561179706155957108692243394547720211763850233539549852279504896,            reHi := (94791457747288810769915033450769834624521877881698843764781164957360751513814679 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/144485983920890870374119804103971405794828929698480141175900155693033234853003264, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C37_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C37_b1

namespace VerifiedLcalc.Certificates.Batch.C37_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -23, a6 := -50 },   conductor := 37,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   geometricUpper := (3206162929939955 : Rat)/9007199254740992,   tail := (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,   box := { reLo := (30283418204113213282209638897320898491570332611770748800561922881321558428265531 : Rat)/216728975881336305561179706155957108692243394547720211763850233539549852279504896,            reHi := (94791457747288810769915033450769834624521877881698843764781164957360751513814679 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/144485983920890870374119804103971405794828929698480141175900155693033234853003264, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C37_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C37_b2

namespace VerifiedLcalc.Certificates.Batch.C37_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -3, a6 := 1 },   conductor := 37,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 0, 1, -2],   alphaLo := (1349303770452201895858762940416 : Rat)/1306263306848253154754638671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5225053227393012523651123046875,   geometricUpper := (3206162929939955 : Rat)/9007199254740992,   tail := (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,   box := { reLo := (30283418204113213282209638897320898491570332611770748800561922881321558428265531 : Rat)/216728975881336305561179706155957108692243394547720211763850233539549852279504896,            reHi := (94791457747288810769915033450769834624521877881698843764781164957360751513814679 : Rat)/72242991960445435187059902051985702897414464849240070587950077846516617426501632,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (42348492506292188466853185821455067457040903258498350854054156567803234746484375 : Rat)/144485983920890870374119804103971405794828929698480141175900155693033234853003264, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C37_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C37_b3

namespace VerifiedLcalc.Certificates.Batch.C38_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -86, a6 := -2456 },   conductor := 38,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1323797827087810039520263671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5295191308351240062713623046875,   geometricUpper := (3250331285048491 : Rat)/9007199254740992,   tail := (1314581500302104086744217349782731469912128957323758620022955790360719321112645399855487089511781704084845980133 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,   box := { reLo := (4297404767088620891680848622281043711371988788430509758557678978259252003253216697643303181126672852213981550107 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,            reHi := (6926567767692836475806712595178257193691602733250417570144730608297505969501346933397669567680051565365057251813 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (1314581500302104086744217349782731469912128957323758620022955790360719321112645399855487089511781704084845980133 : Rat)/17799756781361721214819462108435044767120771064084507561238298040871432041291382568233714142672601296636559228928, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C38_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C38_a1

namespace VerifiedLcalc.Certificates.Batch.C38_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -16, a6 := 22 },   conductor := 38,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1323797827087810039520263671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5295191308351240062713623046875,   geometricUpper := (3250331285048491 : Rat)/9007199254740992,   tail := (1314581500302104086744217349782731469912128957323758620022955790360719321112645399855487089511781704084845980133 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,   box := { reLo := (4297404767088620891680848622281043711371988788430509758557678978259252003253216697643303181126672852213981550107 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,            reHi := (6926567767692836475806712595178257193691602733250417570144730608297505969501346933397669567680051565365057251813 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (1314581500302104086744217349782731469912128957323758620022955790360719321112645399855487089511781704084845980133 : Rat)/17799756781361721214819462108435044767120771064084507561238298040871432041291382568233714142672601296636559228928, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C38_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C38_a2

namespace VerifiedLcalc.Certificates.Batch.C38_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 9, a6 := 90 },   conductor := 38,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1323797827087810039520263671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5295191308351240062713623046875,   geometricUpper := (3250331285048491 : Rat)/9007199254740992,   tail := (1314581500302104086744217349782731469912128957323758620022955790360719321112645399855487089511781704084845980133 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,   box := { reLo := (4297404767088620891680848622281043711371988788430509758557678978259252003253216697643303181126672852213981550107 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,            reHi := (6926567767692836475806712595178257193691602733250417570144730608297505969501346933397669567680051565365057251813 : Rat)/8899878390680860607409731054217522383560385532042253780619149020435716020645691284116857071336300648318279614464,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (1314581500302104086744217349782731469912128957323758620022955790360719321112645399855487089511781704084845980133 : Rat)/17799756781361721214819462108435044767120771064084507561238298040871432041291382568233714142672601296636559228928, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C38_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C38_a3

namespace VerifiedLcalc.Certificates.Batch.C38_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -70, a6 := -279 },   conductor := 38,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1323797827087810039520263671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5295191308351240062713623046875,   geometricUpper := (3250331285048491 : Rat)/9007199254740992,   tail := (226734787126816165296998385598779798489795036874812710147741587726679289677156875 : Rat)/355982055269552806005834385733966423275440627694679694722640375747864996402429952,   box := { reLo := (205218300617843371893250723897680095312238025150710720668244399419930081911818719 : Rat)/1067946165808658418017503157201899269826321883084039084167921127243594989207289856,            reHi := (521875674459580404465703460607288730045183527067125086990316794996788229533012491 : Rat)/355982055269552806005834385733966423275440627694679694722640375747864996402429952,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (226734787126816165296998385598779798489795036874812710147741587726679289677156875 : Rat)/711964110539105612011668771467932846550881255389359389445280751495729992804859904, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C38_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C38_b1

namespace VerifiedLcalc.Certificates.Batch.C38_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 0, a6 := 1 },   conductor := 38,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1323797827087810039520263671875,   alphaHi := (5397215081808807583452231630848 : Rat)/5295191308351240062713623046875,   geometricUpper := (3250331285048491 : Rat)/9007199254740992,   tail := (226734787126816165296998385598779798489795036874812710147741587726679289677156875 : Rat)/355982055269552806005834385733966423275440627694679694722640375747864996402429952,   box := { reLo := (205218300617843371893250723897680095312238025150710720668244399419930081911818719 : Rat)/1067946165808658418017503157201899269826321883084039084167921127243594989207289856,            reHi := (521875674459580404465703460607288730045183527067125086990316794996788229533012491 : Rat)/355982055269552806005834385733966423275440627694679694722640375747864996402429952,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (226734787126816165296998385598779798489795036874812710147741587726679289677156875 : Rat)/711964110539105612011668771467932846550881255389359389445280751495729992804859904, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C38_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C38_b2

namespace VerifiedLcalc.Certificates.Batch.C39_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -69, a6 := -252 },   conductor := 39,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (337325942613050473964690735104 : Rat)/335275777083832263946533203125,   alphaHi := (5397215081808807583452231630848 : Rat)/5364412433341316127777099609375,   geometricUpper := (205835204041789 : Rat)/562949953421312,   tail := (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/334628853160970777435117212527492673596298470529818817916057937752545558528,   box := { reLo := (133852848027664817982447373582839168446069361448872832284256168752260144137 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            reHi := (1519426253772076879309159117985528874915039776543343511947218436333977117687 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/669257706321941554870234425054985347192596941059637635832115875505091117056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C39_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C39_a1

namespace VerifiedLcalc.Certificates.Batch.C39_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -19, a6 := 22 },   conductor := 39,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (337325942613050473964690735104 : Rat)/335275777083832263946533203125,   alphaHi := (5397215081808807583452231630848 : Rat)/5364412433341316127777099609375,   geometricUpper := (205835204041789 : Rat)/562949953421312,   tail := (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/334628853160970777435117212527492673596298470529818817916057937752545558528,   box := { reLo := (133852848027664817982447373582839168446069361448872832284256168752260144137 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            reHi := (1519426253772076879309159117985528874915039776543343511947218436333977117687 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/669257706321941554870234425054985347192596941059637635832115875505091117056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C39_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C39_a2

namespace VerifiedLcalc.Certificates.Batch.C39_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := -4, a6 := -5 },   conductor := 39,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (337325942613050473964690735104 : Rat)/335275777083832263946533203125,   alphaHi := (5397215081808807583452231630848 : Rat)/5364412433341316127777099609375,   geometricUpper := (205835204041789 : Rat)/562949953421312,   tail := (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/334628853160970777435117212527492673596298470529818817916057937752545558528,   box := { reLo := (133852848027664817982447373582839168446069361448872832284256168752260144137 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            reHi := (1519426253772076879309159117985528874915039776543343511947218436333977117687 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/669257706321941554870234425054985347192596941059637635832115875505091117056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C39_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C39_a3

namespace VerifiedLcalc.Certificates.Batch.C39_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 0, a4 := 1, a6 := 0 },   conductor := 39,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, -1],   alphaLo := (337325942613050473964690735104 : Rat)/335275777083832263946533203125,   alphaHi := (5397215081808807583452231630848 : Rat)/5364412433341316127777099609375,   geometricUpper := (205835204041789 : Rat)/562949953421312,   tail := (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/334628853160970777435117212527492673596298470529818817916057937752545558528,   box := { reLo := (133852848027664817982447373582839168446069361448872832284256168752260144137 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            reHi := (1519426253772076879309159117985528874915039776543343511947218436333977117687 : Rat)/1003886559482912332305351637582478020788895411589456453748173813257636675584,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (230928900957401932822648315062875061976759859792459643329063880522129968125 : Rat)/669257706321941554870234425054985347192596941059637635832115875505091117056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C39_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C39_a4

namespace VerifiedLcalc.Certificates.Batch.C40_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -107, a6 := -426 },   conductor := 40,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5432751652517836475372314453125,   alphaHi := (1349303770452201895863057907712 : Rat)/1358187913129459095001220703125,   geometricUpper := (3335309064832211 : Rat)/9007199254740992,   tail := (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/60847057247091080905847544619349012303459557276619330172128815524520278480285775639801252867249536625278858559488,   box := { reLo := (171039340869934773392466801149128272294543987513869941015034264275667882910232264862228726354740654991898510359993 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            reHi := (281280747683886729825794363439811067286084440237302985721465314611389429090281385388268700818140469977471753126471 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/121694114494182161811695089238698024606919114553238660344257631049040556960571551279602505734499073250557717118976, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C40_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C40_a1

namespace VerifiedLcalc.Certificates.Batch.C40_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -7, a6 := -6 },   conductor := 40,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5432751652517836475372314453125,   alphaHi := (1349303770452201895863057907712 : Rat)/1358187913129459095001220703125,   geometricUpper := (3335309064832211 : Rat)/9007199254740992,   tail := (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/60847057247091080905847544619349012303459557276619330172128815524520278480285775639801252867249536625278858559488,   box := { reLo := (171039340869934773392466801149128272294543987513869941015034264275667882910232264862228726354740654991898510359993 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            reHi := (281280747683886729825794363439811067286084440237302985721465314611389429090281385388268700818140469977471753126471 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/121694114494182161811695089238698024606919114553238660344257631049040556960571551279602505734499073250557717118976, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C40_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C40_a2

namespace VerifiedLcalc.Certificates.Batch.C40_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -2, a6 := 1 },   conductor := 40,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5432751652517836475372314453125,   alphaHi := (1349303770452201895863057907712 : Rat)/1358187913129459095001220703125,   geometricUpper := (3335309064832211 : Rat)/9007199254740992,   tail := (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/60847057247091080905847544619349012303459557276619330172128815524520278480285775639801252867249536625278858559488,   box := { reLo := (171039340869934773392466801149128272294543987513869941015034264275667882910232264862228726354740654991898510359993 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            reHi := (281280747683886729825794363439811067286084440237302985721465314611389429090281385388268700818140469977471753126471 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/121694114494182161811695089238698024606919114553238660344257631049040556960571551279602505734499073250557717118976, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C40_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C40_a3

namespace VerifiedLcalc.Certificates.Batch.C40_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 13, a6 := -34 },   conductor := 40,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5432751652517836475372314453125,   alphaHi := (1349303770452201895863057907712 : Rat)/1358187913129459095001220703125,   geometricUpper := (3335309064832211 : Rat)/9007199254740992,   tail := (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/60847057247091080905847544619349012303459557276619330172128815524520278480285775639801252867249536625278858559488,   box := { reLo := (171039340869934773392466801149128272294543987513869941015034264275667882910232264862228726354740654991898510359993 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            reHi := (281280747683886729825794363439811067286084440237302985721465314611389429090281385388268700818140469977471753126471 : Rat)/304235286235455404529237723096745061517297786383096650860644077622601392401428878199006264336247683126394292797440,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (11024140681395187536876283860406977466892545164606790233690838230112754598902188016720333108549452194417278346971 : Rat)/121694114494182161811695089238698024606919114553238660344257631049040556960571551279602505734499073250557717118976, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C40_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C40_a4

namespace VerifiedLcalc.Certificates.Batch.C42_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -1344, a6 := 18405 },   conductor := 42,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/5566913870703591823577880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/2783456935351795864105224609375,   geometricUpper := (1708063807818389 : Rat)/4503599627370496,   tail := (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/10510597337640666239611460632718710288922493768544791809427575703449629714546688,   box := { reLo := (373183062112005598972954619667885008794410017842129300520780876665162750845281 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            reHi := (54892664990144334813250171750002015313769714021983188536276727480230669941382815 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/21021194675281332479222921265437420577844987537089583618855151406899259429093376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C42_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C42_a1

namespace VerifiedLcalc.Certificates.Batch.C42_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -914, a6 := -10915 },   conductor := 42,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/5566913870703591823577880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/2783456935351795864105224609375,   geometricUpper := (1708063807818389 : Rat)/4503599627370496,   tail := (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/10510597337640666239611460632718710288922493768544791809427575703449629714546688,   box := { reLo := (373183062112005598972954619667885008794410017842129300520780876665162750845281 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            reHi := (54892664990144334813250171750002015313769714021983188536276727480230669941382815 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/21021194675281332479222921265437420577844987537089583618855151406899259429093376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C42_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C42_a2

namespace VerifiedLcalc.Certificates.Batch.C42_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -104, a6 := 101 },   conductor := 42,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/5566913870703591823577880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/2783456935351795864105224609375,   geometricUpper := (1708063807818389 : Rat)/4503599627370496,   tail := (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/10510597337640666239611460632718710288922493768544791809427575703449629714546688,   box := { reLo := (373183062112005598972954619667885008794410017842129300520780876665162750845281 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            reHi := (54892664990144334813250171750002015313769714021983188536276727480230669941382815 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/21021194675281332479222921265437420577844987537089583618855151406899259429093376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C42_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C42_a3

namespace VerifiedLcalc.Certificates.Batch.C42_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -84, a6 := 261 },   conductor := 42,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/5566913870703591823577880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/2783456935351795864105224609375,   geometricUpper := (1708063807818389 : Rat)/4503599627370496,   tail := (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/10510597337640666239611460632718710288922493768544791809427575703449629714546688,   box := { reLo := (373183062112005598972954619667885008794410017842129300520780876665162750845281 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            reHi := (54892664990144334813250171750002015313769714021983188536276727480230669941382815 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/21021194675281332479222921265437420577844987537089583618855151406899259429093376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C42_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C42_a4

namespace VerifiedLcalc.Certificates.Batch.C42_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -4, a6 := 5 },   conductor := 42,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/5566913870703591823577880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/2783456935351795864105224609375,   geometricUpper := (1708063807818389 : Rat)/4503599627370496,   tail := (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/10510597337640666239611460632718710288922493768544791809427575703449629714546688,   box := { reLo := (373183062112005598972954619667885008794410017842129300520780876665162750845281 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            reHi := (54892664990144334813250171750002015313769714021983188536276727480230669941382815 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/21021194675281332479222921265437420577844987537089583618855151406899259429093376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C42_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C42_a5

namespace VerifiedLcalc.Certificates.Batch.C42_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 386, a6 := 1277 },   conductor := 42,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, 1, -1, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/5566913870703591823577880859375,   alphaHi := (2698607540904403791726115815424 : Rat)/2783456935351795864105224609375,   geometricUpper := (1708063807818389 : Rat)/4503599627370496,   tail := (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/10510597337640666239611460632718710288922493768544791809427575703449629714546688,   box := { reLo := (373183062112005598972954619667885008794410017842129300520780876665162750845281 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            reHi := (54892664990144334813250171750002015313769714021983188536276727480230669941382815 : Rat)/31531792012921998718834381898156130866767481305634375428282727110348889143640064,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (9086580321338717937738159754523086799558987649226587521440700158109095131843125 : Rat)/21021194675281332479222921265437420577844987537089583618855151406899259429093376, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C42_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C42_a6

namespace VerifiedLcalc.Certificates.Batch.C44_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -77, a6 := -289 },   conductor := 44,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5697918003071719455718994140625,   alphaHi := (168662971306525236982882238464 : Rat)/178059937595991230010986328125,   geometricUpper := (1746565292100897 : Rat)/4503599627370496,   tail := (119038087031053987544499736064039311962090423446722081472787609211880452362038618366683583150718540561237691713 : Rat)/454298589782725938966761742670698552776557635698731782882585217736687020776093648104021923160457200012789547008,   box := { reLo := (246212943404767110943930243253857320123058218713342111401144951867615341977625793743256743206009463236330500799 : Rat)/454298589782725938966761742670698552776557635698731782882585217736687020776093648104021923160457200012789547008,            reHi := (7264336762003130728974184728115859911935380143726099421941561844621873326481960619347027542140392668572399470287 : Rat)/6814478846740889084501426140060478291648364535480976743238778266050305311641404721560328847406858000191843205120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (119038087031053987544499736064039311962090423446722081472787609211880452362038618366683583150718540561237691713 : Rat)/908597179565451877933523485341397105553115271397463565765170435473374041552187296208043846320914400025579094016, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 11, 11, 11] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C44_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C44_a1

namespace VerifiedLcalc.Certificates.Batch.C44_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 3, a6 := -1 },   conductor := 44,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5697918003071719455718994140625,   alphaHi := (168662971306525236982882238464 : Rat)/178059937595991230010986328125,   geometricUpper := (1746565292100897 : Rat)/4503599627370496,   tail := (119038087031053987544499736064039311962090423446722081472787609211880452362038618366683583150718540561237691713 : Rat)/454298589782725938966761742670698552776557635698731782882585217736687020776093648104021923160457200012789547008,   box := { reLo := (246212943404767110943930243253857320123058218713342111401144951867615341977625793743256743206009463236330500799 : Rat)/454298589782725938966761742670698552776557635698731782882585217736687020776093648104021923160457200012789547008,            reHi := (7264336762003130728974184728115859911935380143726099421941561844621873326481960619347027542140392668572399470287 : Rat)/6814478846740889084501426140060478291648364535480976743238778266050305311641404721560328847406858000191843205120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (119038087031053987544499736064039311962090423446722081472787609211880452362038618366683583150718540561237691713 : Rat)/908597179565451877933523485341397105553115271397463565765170435473374041552187296208043846320914400025579094016, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 11] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C44_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C44_a2

namespace VerifiedLcalc.Certificates.Batch.C45_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -19440, a6 := 1048135 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 2],                kodaira := -8 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a1

namespace VerifiedLcalc.Certificates.Batch.C45_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1215, a6 := 16600 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [0, 1, 2, 1, 0, 2, 0],                kodaira := -12 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a2

namespace VerifiedLcalc.Certificates.Batch.C45_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -990, a6 := 22765 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1, 0, 2, 2, 1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0],                kodaira := -20 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a3

namespace VerifiedLcalc.Certificates.Batch.C45_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -720, a6 := -7259 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a4

namespace VerifiedLcalc.Certificates.Batch.C45_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -90, a6 := 175 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2, 0, 2],                kodaira := -8 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a5

namespace VerifiedLcalc.Certificates.Batch.C45_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -45, a6 := -104 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 2,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a6

namespace VerifiedLcalc.Certificates.Batch.C45_a7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 0, a6 := -5 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a7.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a7

namespace VerifiedLcalc.Certificates.Batch.C45_a8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 315, a6 := 1066 },   conductor := 45,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, -1, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/2881151650498338222503662109375,   alphaHi := (5397215081808807583452231630848 : Rat)/5762303300996676349639892578125,   geometricUpper := (3530297731634159 : Rat)/9007199254740992,   tail := (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/57515111131567377946208685689080469872554593644556125483072403450046359177896444646802718671168309580941024559104,   box := { reLo := (183102506613501725083428840022023295014651942633824137418714514912662625637197469834757114007129044789492007661589 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            reHi := (347188494310499938619385422580896304272267040497106461521767051093496025216932896244550725248632172741530687279083 : Rat)/287575555657836889731043428445402349362772968222780627415362017250231795889482223234013593355841547904705122795520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16408598769699802516488468824367791342546256719794895205664062626325949257285276820289082506771479672881635427119 : Rat)/115030222263134755892417371378160939745109187289112250966144806900092718355792889293605437342336619161882049118208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C45_a8.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C45_a8

namespace VerifiedLcalc.Certificates.Batch.C46_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -170, a6 := -812 },   conductor := 46,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 0, 1, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5825977093640651798248291015625,   alphaHi := (674651885226100947931528953856 : Rat)/728247136705081462860107421875,   geometricUpper := (3566622402440897 : Rat)/9007199254740992,   tail := (17627555544180830024625357673987710315850801996739785291931528336523178674741768659902754538145049392614114711713 : Rat)/56894398924149081032389204639715342146134133190856368082033415080430775155354411386762518780969055003173348966400,   box := { reLo := (20094674826204469430056591050659293953589626109667800015510649107118224732177181755527083756995548032068393248607 : Rat)/56894398924149081032389204639715342146134133190856368082033415080430775155354411386762518780969055003173348966400,            reHi := (55349785914566161693697851876147650051931279794996721307965950639502744744183539997633595389372812067744144545953 : Rat)/56894398924149081032389204639715342146134133190856368082033415080430775155354411386762518780969055003173348966400,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (17627555544180830024625357673987710315850801996739785291931528336523178674741768659902754538145049392614114711713 : Rat)/113788797848298162064778409279430684292268266381712736164066830160861550310708822773525037561938110006346697932800, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C46_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C46_a1

namespace VerifiedLcalc.Certificates.Batch.C46_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -10, a6 := -12 },   conductor := 46,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 0, 1, 4, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/5825977093640651798248291015625,   alphaHi := (674651885226100947931528953856 : Rat)/728247136705081462860107421875,   geometricUpper := (3566622402440897 : Rat)/9007199254740992,   tail := (17627555544180830024625357673987710315850801996739785291931528336523178674741768659902754538145049392614114711713 : Rat)/56894398924149081032389204639715342146134133190856368082033415080430775155354411386762518780969055003173348966400,   box := { reLo := (20094674826204469430056591050659293953589626109667800015510649107118224732177181755527083756995548032068393248607 : Rat)/56894398924149081032389204639715342146134133190856368082033415080430775155354411386762518780969055003173348966400,            reHi := (55349785914566161693697851876147650051931279794996721307965950639502744744183539997633595389372812067744144545953 : Rat)/56894398924149081032389204639715342146134133190856368082033415080430775155354411386762518780969055003173348966400,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (17627555544180830024625357673987710315850801996739785291931528336523178674741768659902754538145049392614114711713 : Rat)/113788797848298162064778409279430684292268266381712736164066830160861550310708822773525037561938110006346697932800, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C46_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C46_a2

namespace VerifiedLcalc.Certificates.Batch.C48_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -384, a6 := 2772 },   conductor := 48,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/5951281258814973735809326171875,   geometricUpper := (3636873895192135 : Rat)/9007199254740992,   tail := (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/55693948701983191782971237786042798485958157419651498056586378700230251556433854861076034249890029678073737117696,   box := { reLo := (401026537766847503045639301855471603436638721158542903702417762661822989913797264231280926529636486149396439242471 : Rat)/835409230529747876744568566790641977289372361294772470848795680503453773346507822916140513748350445171106056765440,            reHi := (335739937104109350618440346769517149809728449000727829430852266563725147408750850753631214541295394444001453886899 : Rat)/278469743509915958914856188930213992429790787098257490282931893501151257782169274305380171249450148390368685588480,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/111387897403966383565942475572085596971916314839302996113172757400460503112867709722152068499780059356147474235392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C48_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C48_a1

namespace VerifiedLcalc.Certificates.Batch.C48_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -64, a6 := -220 },   conductor := 48,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/5951281258814973735809326171875,   geometricUpper := (3636873895192135 : Rat)/9007199254740992,   tail := (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/55693948701983191782971237786042798485958157419651498056586378700230251556433854861076034249890029678073737117696,   box := { reLo := (401026537766847503045639301855471603436638721158542903702417762661822989913797264231280926529636486149396439242471 : Rat)/835409230529747876744568566790641977289372361294772470848795680503453773346507822916140513748350445171106056765440,            reHi := (335739937104109350618440346769517149809728449000727829430852266563725147408750850753631214541295394444001453886899 : Rat)/278469743509915958914856188930213992429790787098257490282931893501151257782169274305380171249450148390368685588480,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/111387897403966383565942475572085596971916314839302996113172757400460503112867709722152068499780059356147474235392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [0], kodaira := -6 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C48_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C48_a2

namespace VerifiedLcalc.Certificates.Batch.C48_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -24, a6 := 36 },   conductor := 48,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/5951281258814973735809326171875,   geometricUpper := (3636873895192135 : Rat)/9007199254740992,   tail := (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/55693948701983191782971237786042798485958157419651498056586378700230251556433854861076034249890029678073737117696,   box := { reLo := (401026537766847503045639301855471603436638721158542903702417762661822989913797264231280926529636486149396439242471 : Rat)/835409230529747876744568566790641977289372361294772470848795680503453773346507822916140513748350445171106056765440,            reHi := (335739937104109350618440346769517149809728449000727829430852266563725147408750850753631214541295394444001453886899 : Rat)/278469743509915958914856188930213992429790787098257490282931893501151257782169274305380171249450148390368685588480,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/111387897403966383565942475572085596971916314839302996113172757400460503112867709722152068499780059356147474235392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [1], kodaira := -6 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C48_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C48_a3

namespace VerifiedLcalc.Certificates.Batch.C48_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -4, a6 := -4 },   conductor := 48,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/5951281258814973735809326171875,   geometricUpper := (3636873895192135 : Rat)/9007199254740992,   tail := (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/55693948701983191782971237786042798485958157419651498056586378700230251556433854861076034249890029678073737117696,   box := { reLo := (401026537766847503045639301855471603436638721158542903702417762661822989913797264231280926529636486149396439242471 : Rat)/835409230529747876744568566790641977289372361294772470848795680503453773346507822916140513748350445171106056765440,            reHi := (335739937104109350618440346769517149809728449000727829430852266563725147408750850753631214541295394444001453886899 : Rat)/278469743509915958914856188930213992429790787098257490282931893501151257782169274305380171249450148390368685588480,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/111387897403966383565942475572085596971916314839302996113172757400460503112867709722152068499780059356147474235392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -1 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C48_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C48_a4

namespace VerifiedLcalc.Certificates.Batch.C48_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 1, a6 := 0 },   conductor := 48,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/5951281258814973735809326171875,   geometricUpper := (3636873895192135 : Rat)/9007199254740992,   tail := (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/55693948701983191782971237786042798485958157419651498056586378700230251556433854861076034249890029678073737117696,   box := { reLo := (401026537766847503045639301855471603436638721158542903702417762661822989913797264231280926529636486149396439242471 : Rat)/835409230529747876744568566790641977289372361294772470848795680503453773346507822916140513748350445171106056765440,            reHi := (335739937104109350618440346769517149809728449000727829430852266563725147408750850753631214541295394444001453886899 : Rat)/278469743509915958914856188930213992429790787098257490282931893501151257782169274305380171249450148390368685588480,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/111387897403966383565942475572085596971916314839302996113172757400460503112867709722152068499780059356147474235392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C48_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C48_a5

namespace VerifiedLcalc.Certificates.Batch.C48_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 16, a6 := 180 },   conductor := 48,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, 0, -2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1487820314703743457794189453125,   alphaHi := (5397215081808807583452231630848 : Rat)/5951281258814973735809326171875,   geometricUpper := (3636873895192135 : Rat)/9007199254740992,   tail := (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/55693948701983191782971237786042798485958157419651498056586378700230251556433854861076034249890029678073737117696,   box := { reLo := (401026537766847503045639301855471603436638721158542903702417762661822989913797264231280926529636486149396439242471 : Rat)/835409230529747876744568566790641977289372361294772470848795680503453773346507822916140513748350445171106056765440,            reHi := (335739937104109350618440346769517149809728449000727829430852266563725147408750850753631214541295394444001453886899 : Rat)/278469743509915958914856188930213992429790787098257490282931893501151257782169274305380171249450148390368685588480,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (20206442451516007575987333201193681135365696661943884814347402761013654331688324955916131481401624261600281484375 : Rat)/111387897403966383565942475572085596971916314839302996113172757400460503112867709722152068499780059356147474235392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0,              s := 1,              t := 0,              starT := 1,              cubicRoot := 1,              quadraticRoot := 0,              chain := [1, 1],              kodaira := -7 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C48_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C48_a6

namespace VerifiedLcalc.Certificates.Batch.C49_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -1822, a6 := 30393 },   conductor := 49,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6012954214400000095367431640625,   alphaHi := (314159265358979323847 : Rat)/350000000000000000000,   geometricUpper := (3670861125855755 : Rat)/9007199254740992,   tail := (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,   box := { reLo := (31750359661381029037735146518149157590681705009731336543786151654705650178137899349132166946507601655558462032925 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            reHi := (74882185148904084218825514505319312008818071542509048723827070849885431884870367843345362164698261597080026821603 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/110226356858616848373022269132700616310088688415046636515594371766270433789449709492655978907200355291230185193472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [7, 7, 7, 7, 7, 7, 7, 7, 7] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C49_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C49_a1

namespace VerifiedLcalc.Certificates.Batch.C49_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -107, a6 := 552 },   conductor := 49,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6012954214400000095367431640625,   alphaHi := (314159265358979323847 : Rat)/350000000000000000000,   geometricUpper := (3670861125855755 : Rat)/9007199254740992,   tail := (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,   box := { reLo := (31750359661381029037735146518149157590681705009731336543786151654705650178137899349132166946507601655558462032925 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            reHi := (74882185148904084218825514505319312008818071542509048723827070849885431884870367843345362164698261597080026821603 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/110226356858616848373022269132700616310088688415046636515594371766270433789449709492655978907200355291230185193472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [7, 7, 7, 7, 7, 7, 7, 7, 7] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C49_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C49_a2

namespace VerifiedLcalc.Certificates.Batch.C49_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -37, a6 := -78 },   conductor := 49,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6012954214400000095367431640625,   alphaHi := (314159265358979323847 : Rat)/350000000000000000000,   geometricUpper := (3670861125855755 : Rat)/9007199254740992,   tail := (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,   box := { reLo := (31750359661381029037735146518149157590681705009731336543786151654705650178137899349132166946507601655558462032925 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            reHi := (74882185148904084218825514505319312008818071542509048723827070849885431884870367843345362164698261597080026821603 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/110226356858616848373022269132700616310088688415046636515594371766270433789449709492655978907200355291230185193472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [7, 7, 7] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C49_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C49_a3

namespace VerifiedLcalc.Certificates.Batch.C49_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -2, a6 := -1 },   conductor := 49,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6012954214400000095367431640625,   alphaHi := (314159265358979323847 : Rat)/350000000000000000000,   geometricUpper := (3670861125855755 : Rat)/9007199254740992,   tail := (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,   box := { reLo := (31750359661381029037735146518149157590681705009731336543786151654705650178137899349132166946507601655558462032925 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            reHi := (74882185148904084218825514505319312008818071542509048723827070849885431884870367843345362164698261597080026821603 : Rat)/55113178429308424186511134566350308155044344207523318257797185883135216894724854746327989453600177645615092596736,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (21565912743761516882659244807356821872084178789476590384940478519548522833897830232698454247170821232903746171875 : Rat)/110226356858616848373022269132700616310088688415046636515594371766270433789449709492655978907200355291230185193472, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [7, 7, 7] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C49_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C49_a4

namespace VerifiedLcalc.Certificates.Batch.C50_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -126, a6 := -552 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (7575447838410857813230520592446319768877978466316038051633706668368156995196802991994327288585499721233261 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (29482970863592809401005060822912495383057218509756533871802574445618126845712974598628094240316978140908691 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 2, 2, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_a1

namespace VerifiedLcalc.Certificates.Batch.C50_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -76, a6 := 298 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (7575447838410857813230520592446319768877978466316038051633706668368156995196802991994327288585499721233261 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (29482970863592809401005060822912495383057218509756533871802574445618126845712974598628094240316978140908691 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_a2

namespace VerifiedLcalc.Certificates.Batch.C50_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1, a6 := -2 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (7575447838410857813230520592446319768877978466316038051633706668368156995196802991994327288585499721233261 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (29482970863592809401005060822912495383057218509756533871802574445618126845712974598628094240316978140908691 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_a3

namespace VerifiedLcalc.Certificates.Batch.C50_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 549, a6 := -2202 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (7575447838410857813230520592446319768877978466316038051633706668368156995196802991994327288585499721233261 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (29482970863592809401005060822912495383057218509756533871802574445618126845712974598628094240316978140908691 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_a4

namespace VerifiedLcalc.Certificates.Batch.C50_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -3138, a6 := -68969 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (13960812855727524637747210872399729095046883043980417301712635228557367112965417167725489734745147128836973 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (35868335880909476225521751102865904709226123087420913121881503005807336963481588774359256686476625548512403 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_b1

namespace VerifiedLcalc.Certificates.Batch.C50_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -13, a6 := -219 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (13960812855727524637747210872399729095046883043980417301712635228557367112965417167725489734745147128836973 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (35868335880909476225521751102865904709226123087420913121881503005807336963481588774359256686476625548512403 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_b2

namespace VerifiedLcalc.Certificates.Batch.C50_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -3, a6 := 1 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (13960812855727524637747210872399729095046883043980417301712635228557367112965417167725489734745147128836973 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (35868335880909476225521751102865904709226123087420913121881503005807336963481588774359256686476625548512403 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_b3

namespace VerifiedLcalc.Certificates.Batch.C50_b4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 22, a6 := -9 },   conductor := 50,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 0, -1],   alphaLo := (2698607540904403791717525880832 : Rat)/3037000499976049709320068359375,   alphaHi := (5397215081808807583452231630848 : Rat)/6074000999952099323272705078125,   geometricUpper := (463015867444315 : Rat)/1125899906842624,   tail := (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,   box := { reLo := (13960812855727524637747210872399729095046883043980417301712635228557367112965417167725489734745147128836973 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            reHi := (35868335880909476225521751102865904709226123087420913121881503005807336963481588774359256686476625548512403 : Rat)/26008956744627497728606604396288505210612670153217640786396451784404084335739072452730592290012761012830208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (10953761512590964965483785978280950192353330351262396279879876833870568825651990953975945426831783934921875 : Rat)/52017913489254995457213208792577010421225340306435281572792903568808168671478144905461184580025522025660416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyTameCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C50_b4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C50_b4

namespace VerifiedLcalc.Certificates.Batch.C51_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -59, a6 := -196 },   conductor := 51,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, -2, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6134440309463242816925048828125,   alphaHi := (1349303770452201895863057907712 : Rat)/1533610077365810680389404296875,   geometricUpper := (3736697686211959 : Rat)/9007199254740992,   tail := (3489071439511011474669800977672645412028069353098037721216925659862544020053584769459165935178621344125897950817 : Rat)/7712595730574944851744588772051220708102806916642363324634667989131202359609554513918870457606077618820766236672,   box := { reLo := (47438528710968296677278715305166928650585618277586668177368367891610530848965359177023479258472636791788617588817 : Rat)/115688935958624172776168831580768310621542103749635449869520019836968035394143317708783056864091164282311493550080,            reHi := (30422134379259742397558806045643024474312034441103885718954440497596103503478790886747907634614088686960182612771 : Rat)/23137787191724834555233766316153662124308420749927089973904003967393607078828663541756611372818232856462298710016,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3489071439511011474669800977672645412028069353098037721216925659862544020053584769459165935178621344125897950817 : Rat)/15425191461149889703489177544102441416205613833284726649269335978262404719219109027837740915212155237641532473344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C51_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C51_a1

namespace VerifiedLcalc.Certificates.Batch.C51_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 1, a6 := -1 },   conductor := 51,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 1, -2, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6134440309463242816925048828125,   alphaHi := (1349303770452201895863057907712 : Rat)/1533610077365810680389404296875,   geometricUpper := (3736697686211959 : Rat)/9007199254740992,   tail := (3489071439511011474669800977672645412028069353098037721216925659862544020053584769459165935178621344125897950817 : Rat)/7712595730574944851744588772051220708102806916642363324634667989131202359609554513918870457606077618820766236672,   box := { reLo := (47438528710968296677278715305166928650585618277586668177368367891610530848965359177023479258472636791788617588817 : Rat)/115688935958624172776168831580768310621542103749635449869520019836968035394143317708783056864091164282311493550080,            reHi := (30422134379259742397558806045643024474312034441103885718954440497596103503478790886747907634614088686960182612771 : Rat)/23137787191724834555233766316153662124308420749927089973904003967393607078828663541756611372818232856462298710016,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3489071439511011474669800977672645412028069353098037721216925659862544020053584769459165935178621344125897950817 : Rat)/15425191461149889703489177544102441416205613833284726649269335978262404719219109027837740915212155237641532473344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C51_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C51_a2

namespace VerifiedLcalc.Certificates.Batch.C52_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -4, a6 := -3 },   conductor := 52,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1548572481216892147064208984375,   alphaHi := (5397215081808807583452231630848 : Rat)/6194289924867568492889404296875,   geometricUpper := (1884299179118385 : Rat)/4503599627370496,   tail := (202507528121337392086020490261043279227316714539553728088304766870549739101568276124442268842443282004441640625 : Rat)/417523865148182225028019057100569998602708500454127747507448221682072296846414059245405379482181188021882191872,   box := { reLo := (151157901964421678913128299267797444276908129010742356062040876745943864358213157821129892907398252575267934543 : Rat)/417523865148182225028019057100569998602708500454127747507448221682072296846414059245405379482181188021882191872,            reHi := (2780864791035483427932906602151467343248877835951114250712628128242143528416527227372642568998665817953971071349 : Rat)/2087619325740911125140095285502849993013542502270638737537241108410361484232070296227026897410905940109410959360,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (202507528121337392086020490261043279227316714539553728088304766870549739101568276124442268842443282004441640625 : Rat)/835047730296364450056038114201139997205417000908255495014896443364144593692828118490810758964362376043764383744, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 13] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C52_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C52_a1

namespace VerifiedLcalc.Certificates.Batch.C52_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := -10 },   conductor := 52,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 2, 0],   alphaLo := (1349303770452201895858762940416 : Rat)/1548572481216892147064208984375,   alphaHi := (5397215081808807583452231630848 : Rat)/6194289924867568492889404296875,   geometricUpper := (1884299179118385 : Rat)/4503599627370496,   tail := (202507528121337392086020490261043279227316714539553728088304766870549739101568276124442268842443282004441640625 : Rat)/417523865148182225028019057100569998602708500454127747507448221682072296846414059245405379482181188021882191872,   box := { reLo := (151157901964421678913128299267797444276908129010742356062040876745943864358213157821129892907398252575267934543 : Rat)/417523865148182225028019057100569998602708500454127747507448221682072296846414059245405379482181188021882191872,            reHi := (2780864791035483427932906602151467343248877835951114250712628128242143528416527227372642568998665817953971071349 : Rat)/2087619325740911125140095285502849993013542502270638737537241108410361484232070296227026897410905940109410959360,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (202507528121337392086020490261043279227316714539553728088304766870549739101568276124442268842443282004441640625 : Rat)/835047730296364450056038114201139997205417000908255495014896443364144593692828118490810758964362376043764383744, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 13, 13] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 0, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C52_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C52_a2

namespace VerifiedLcalc.Certificates.Batch.C54_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -123, a6 := -667 },   conductor := 54,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 0, 1, 3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/6312287002284721088409423828125,   geometricUpper := (3830483190591557 : Rat)/9007199254740992,   tail := (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,   box := { reLo := (7761516690659439574846938944199677882603948520467571588687959012747406677909092705918245803868296314025781129523 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            reHi := (65864319360991991208017500138655521157482623783592052406751882509949576011432946322352906039880221465611631955661 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/104771146283855226915182574596540501047186016081133000479925031389197883920498913100566261568023407327950657290240, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C54_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C54_a1

namespace VerifiedLcalc.Certificates.Batch.C54_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -3, a6 := 3 },   conductor := 54,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 0, 1, 3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/6312287002284721088409423828125,   geometricUpper := (3830483190591557 : Rat)/9007199254740992,   tail := (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,   box := { reLo := (7761516690659439574846938944199677882603948520467571588687959012747406677909092705918245803868296314025781129523 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            reHi := (65864319360991991208017500138655521157482623783592052406751882509949576011432946322352906039880221465611631955661 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/104771146283855226915182574596540501047186016081133000479925031389197883920498913100566261568023407327950657290240, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C54_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C54_a2

namespace VerifiedLcalc.Certificates.Batch.C54_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 12, a6 := 8 },   conductor := 54,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, -1, 0, 1, 3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/6312287002284721088409423828125,   geometricUpper := (3830483190591557 : Rat)/9007199254740992,   tail := (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,   box := { reLo := (7761516690659439574846938944199677882603948520467571588687959012747406677909092705918245803868296314025781129523 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            reHi := (65864319360991991208017500138655521157482623783592052406751882509949576011432946322352906039880221465611631955661 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/104771146283855226915182574596540501047186016081133000479925031389197883920498913100566261568023407327950657290240, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 1,                starT := 1,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C54_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C54_a3

namespace VerifiedLcalc.Certificates.Batch.C54_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -29, a6 := -53 },   conductor := 54,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/6312287002284721088409423828125,   geometricUpper := (3830483190591557 : Rat)/9007199254740992,   tail := (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,   box := { reLo := (24960967090748414806323487589221369668807360106432293294328817296104512884166124446994497866341241440506530394419 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            reHi := (83063769761080966439494048783677212943686035369556774112392740793306682217689978063429158102353166592092381220557 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/104771146283855226915182574596540501047186016081133000479925031389197883920498913100566261568023407327950657290240, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 1,                s := 1,                t := 2,                starT := 2,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C54_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C54_b1

namespace VerifiedLcalc.Certificates.Batch.C54_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -14, a6 := 29 },   conductor := 54,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/6312287002284721088409423828125,   geometricUpper := (3830483190591557 : Rat)/9007199254740992,   tail := (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,   box := { reLo := (24960967090748414806323487589221369668807360106432293294328817296104512884166124446994497866341241440506530394419 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            reHi := (83063769761080966439494048783677212943686035369556774112392740793306682217689978063429158102353166592092381220557 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/104771146283855226915182574596540501047186016081133000479925031389197883920498913100566261568023407327950657290240, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C54_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C54_b2

namespace VerifiedLcalc.Certificates.Batch.C54_b3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := 1, a6 := -1 },   conductor := 54,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -3, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3156143501142360591888427734375,   alphaHi := (5397215081808807583452231630848 : Rat)/6312287002284721088409423828125,   geometricUpper := (3830483190591557 : Rat)/9007199254740992,   tail := (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,   box := { reLo := (24960967090748414806323487589221369668807360106432293294328817296104512884166124446994497866341241440506530394419 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            reHi := (83063769761080966439494048783677212943686035369556774112392740793306682217689978063429158102353166592092381220557 : Rat)/52385573141927613457591287298270250523593008040566500239962515694598941960249456550283130784011703663975328645120,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (29051401335166259241079484396554557118036040955224241344125312464496952198455942524833606629119758319136656690893 : Rat)/104771146283855226915182574596540501047186016081133000479925031389197883920498913100566261568023407327950657290240, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C54_b3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C54_b3

namespace VerifiedLcalc.Certificates.Batch.C55_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -59, a6 := 190 },   conductor := 55,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 1, 0],   alphaLo := (84331485653262618491172683776 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/6370465992544110012054443359375,   geometricUpper := (3860511319054227 : Rat)/9007199254740992,   tail := (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,   box := { reLo := (4547128990500297439929243955871551480421635721824738783688530049069403264333302374888820762919518665972287958625 : Rat)/10374491119410753399133976297770302275289117836262519676174460169811933742672335510240611961978656731558787940352,            reHi := (84102796706590196947196630943814718444506601769140893538161715081726136087543474905699697880657653471481466443803 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/103744911194107533991339762977703022752891178362625196761744601698119337426723355102406119619786567315587879403520, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C55_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C55_a1

namespace VerifiedLcalc.Certificates.Batch.C55_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -29, a6 := -52 },   conductor := 55,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 1, 0],   alphaLo := (84331485653262618491172683776 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/6370465992544110012054443359375,   geometricUpper := (3860511319054227 : Rat)/9007199254740992,   tail := (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,   box := { reLo := (4547128990500297439929243955871551480421635721824738783688530049069403264333302374888820762919518665972287958625 : Rat)/10374491119410753399133976297770302275289117836262519676174460169811933742672335510240611961978656731558787940352,            reHi := (84102796706590196947196630943814718444506601769140893538161715081726136087543474905699697880657653471481466443803 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/103744911194107533991339762977703022752891178362625196761744601698119337426723355102406119619786567315587879403520, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C55_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C55_a2

namespace VerifiedLcalc.Certificates.Batch.C55_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -4, a6 := 3 },   conductor := 55,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 1, 0],   alphaLo := (84331485653262618491172683776 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/6370465992544110012054443359375,   geometricUpper := (3860511319054227 : Rat)/9007199254740992,   tail := (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,   box := { reLo := (4547128990500297439929243955871551480421635721824738783688530049069403264333302374888820762919518665972287958625 : Rat)/10374491119410753399133976297770302275289117836262519676174460169811933742672335510240611961978656731558787940352,            reHi := (84102796706590196947196630943814718444506601769140893538161715081726136087543474905699697880657653471481466443803 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/103744911194107533991339762977703022752891178362625196761744601698119337426723355102406119619786567315587879403520, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C55_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C55_a3

namespace VerifiedLcalc.Certificates.Batch.C55_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 1, a6 := 0 },   conductor := 55,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 1, 0],   alphaLo := (84331485653262618491172683776 : Rat)/99538531133501720428466796875,   alphaHi := (5397215081808807583452231630848 : Rat)/6370465992544110012054443359375,   geometricUpper := (3860511319054227 : Rat)/9007199254740992,   tail := (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,   box := { reLo := (4547128990500297439929243955871551480421635721824738783688530049069403264333302374888820762919518665972287958625 : Rat)/10374491119410753399133976297770302275289117836262519676174460169811933742672335510240611961978656731558787940352,            reHi := (84102796706590196947196630943814718444506601769140893538161715081726136087543474905699697880657653471481466443803 : Rat)/51872455597053766995669881488851511376445589181312598380872300849059668713361677551203059809893283657793939701760,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (30683575877044340764226541396913406151333977098905413984514418725562914382529051259945239309067052373980463487003 : Rat)/103744911194107533991339762977703022752891178362625196761744601698119337426723355102406119619786567315587879403520, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C55_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C55_a4

namespace VerifiedLcalc.Certificates.Batch.C56_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -299, a6 := 1990 },   conductor := 56,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 2, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3214059221806180286407470703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6428118443612360477447509765625,   geometricUpper := (1944978727563229 : Rat)/4503599627370496,   tail := (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/401322524045217024458572307191383964910730431596317363080378557495301380058023968317776880245823352653274415104,   box := { reLo := (493261522546923753467725329521636274174435067209173721859406231640511680389697713055396997112504633179745801143 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            reHi := (3021372593026366238679438360400408879311473190354461896423377322569524514501771106990327853116497479261134793801 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/802645048090434048917144614382767929821460863192634726160757114990602760116047936635553760491646705306548830208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C56_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C56_a1

namespace VerifiedLcalc.Certificates.Batch.C56_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -59, a6 := -138 },   conductor := 56,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 2, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3214059221806180286407470703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6428118443612360477447509765625,   geometricUpper := (1944978727563229 : Rat)/4503599627370496,   tail := (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/401322524045217024458572307191383964910730431596317363080378557495301380058023968317776880245823352653274415104,   box := { reLo := (493261522546923753467725329521636274174435067209173721859406231640511680389697713055396997112504633179745801143 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            reHi := (3021372593026366238679438360400408879311473190354461896423377322569524514501771106990327853116497479261134793801 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/802645048090434048917144614382767929821460863192634726160757114990602760116047936635553760491646705306548830208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C56_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C56_a2

namespace VerifiedLcalc.Certificates.Batch.C56_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := -19, a6 := 30 },   conductor := 56,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 2, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3214059221806180286407470703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6428118443612360477447509765625,   geometricUpper := (1944978727563229 : Rat)/4503599627370496,   tail := (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/401322524045217024458572307191383964910730431596317363080378557495301380058023968317776880245823352653274415104,   box := { reLo := (493261522546923753467725329521636274174435067209173721859406231640511680389697713055396997112504633179745801143 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            reHi := (3021372593026366238679438360400408879311473190354461896423377322569524514501771106990327853116497479261134793801 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/802645048090434048917144614382767929821460863192634726160757114990602760116047936635553760491646705306548830208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C56_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C56_a3

namespace VerifiedLcalc.Certificates.Batch.C56_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 0, a4 := 1, a6 := 2 },   conductor := 56,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 0, 0, 2, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3214059221806180286407470703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6428118443612360477447509765625,   geometricUpper := (1944978727563229 : Rat)/4503599627370496,   tail := (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/401322524045217024458572307191383964910730431596317363080378557495301380058023968317776880245823352653274415104,   box := { reLo := (493261522546923753467725329521636274174435067209173721859406231640511680389697713055396997112504633179745801143 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            reHi := (3021372593026366238679438360400408879311473190354461896423377322569524514501771106990327853116497479261134793801 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/802645048090434048917144614382767929821460863192634726160757114990602760116047936635553760491646705306548830208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C56_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C56_a4

namespace VerifiedLcalc.Certificates.Batch.C56_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -40, a6 := -84 },   conductor := 56,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 2, 0, -4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3214059221806180286407470703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6428118443612360477447509765625,   geometricUpper := (1944978727563229 : Rat)/4503599627370496,   tail := (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/401322524045217024458572307191383964910730431596317363080378557495301380058023968317776880245823352653274415104,   box := { reLo := (212139875817405224341314344588624373799245626649624836217077337171321813460402722875942602609047518118831714621 : Rat)/668870873408695040764287178652306608184550719327195605133964262492168966763373280529628133743038921088790691840,            reHi := (3164530697931658633496996326706467973858208044145172509712168240047586401232448974438987392669690847740362239049 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/802645048090434048917144614382767929821460863192634726160757114990602760116047936635553760491646705306548830208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C56_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C56_b1

namespace VerifiedLcalc.Certificates.Batch.C56_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 0, a6 := -4 },   conductor := 56,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 0, 2, 0, -4, 0],   alphaLo := (2698607540904403791717525880832 : Rat)/3214059221806180286407470703125,   alphaHi := (5397215081808807583452231630848 : Rat)/6428118443612360477447509765625,   geometricUpper := (1944978727563229 : Rat)/4503599627370496,   tail := (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/401322524045217024458572307191383964910730431596317363080378557495301380058023968317776880245823352653274415104,   box := { reLo := (212139875817405224341314344588624373799245626649624836217077337171321813460402722875942602609047518118831714621 : Rat)/668870873408695040764287178652306608184550719327195605133964262492168966763373280529628133743038921088790691840,            reHi := (3164530697931658633496996326706467973858208044145172509712168240047586401232448974438987392669690847740362239049 : Rat)/2006612620226085122292861535956919824553652157981586815401892787476506900290119841588884401229116763266372075520,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (252811107047944186143120393692263090552503225676583777728670434782296466776691616584738064940338882149688648309 : Rat)/802645048090434048917144614382767929821460863192634726160757114990602760116047936635553760491646705306548830208, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C56_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C56_b2

namespace VerifiedLcalc.Certificates.Batch.C57_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -4390, a6 := -113432 },   conductor := 57,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -2, 1, 2, 1, -2, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   geometricUpper := (3918841013586029 : Rat)/9007199254740992,   tail := (1430173870983149371472474595112865220895828423788294346755112985011716692503716428693811955567141841398970745281882546171736459901436675624830509 : Rat)/7315061634062461376938357533902334764072726652540108509045820186914226688212259831480336819137277409497111339869215128957755591569218872138530816,   box := { reLo := (300350758138455691608688228229326071247841948145144008451226689425532227233925346375734132143458902223358559077423365416824434141840398621783947147 : Rat)/768081471576558444578527541059745150227636298516711393449811119625993802262287282305435366009414127997196690686267588540564337114767981574545735680,            reHi := (200229090348305959145946019637134596421997217762834765023907635635312069197378448359408385189609019601414170913174413066776023079503226252226353191 : Rat)/256027157192186148192842513686581716742545432838903797816603706541997934087429094101811788669804709332398896895422529513521445704922660524848578560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (1430173870983149371472474595112865220895828423788294346755112985011716692503716428693811955567141841398970745281882546171736459901436675624830509 : Rat)/14630123268124922753876715067804669528145453305080217018091640373828453376424519662960673638274554818994222679738430257915511183138437744277061632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C57_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C57_b1

namespace VerifiedLcalc.Certificates.Batch.C57_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 20, a6 := -32 },   conductor := 57,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 8,   coefficients := [1, -2, 1, 2, 1, -2, 3, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   geometricUpper := (3918841013586029 : Rat)/9007199254740992,   tail := (1430173870983149371472474595112865220895828423788294346755112985011716692503716428693811955567141841398970745281882546171736459901436675624830509 : Rat)/7315061634062461376938357533902334764072726652540108509045820186914226688212259831480336819137277409497111339869215128957755591569218872138530816,   box := { reLo := (300350758138455691608688228229326071247841948145144008451226689425532227233925346375734132143458902223358559077423365416824434141840398621783947147 : Rat)/768081471576558444578527541059745150227636298516711393449811119625993802262287282305435366009414127997196690686267588540564337114767981574545735680,            reHi := (200229090348305959145946019637134596421997217762834765023907635635312069197378448359408385189609019601414170913174413066776023079503226252226353191 : Rat)/256027157192186148192842513686581716742545432838903797816603706541997934087429094101811788669804709332398896895422529513521445704922660524848578560,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (1430173870983149371472474595112865220895828423788294346755112985011716692503716428693811955567141841398970745281882546171736459901436675624830509 : Rat)/14630123268124922753876715067804669528145453305080217018091640373828453376424519662960673638274554818994222679738430257915511183138437744277061632, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C57_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C57_b2

namespace VerifiedLcalc.Certificates.Batch.C57_c1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -102, a6 := 385 },   conductor := 57,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, -1, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   geometricUpper := (3918841013586029 : Rat)/9007199254740992,   tail := (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/50875723826420520027794455673794989613675918461221180898203692932636351080332711399071641591589898383835627782144,   box := { reLo := (35305005144618055427943386262212779760265150439693968199682943164601684273597449502583860571821015961892653156397 : Rat)/84792873044034200046324092789658316022793197435368634830339488221060585133887852331786069319316497306392712970240,            reHi := (446711944261783561776710034530803438359861041877892529751137932250291620966657504592234823367693884799665299892089 : Rat)/254378619132102600138972278368974948068379592306105904491018464663181755401663556995358207957949491919178138910720,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/101751447652841040055588911347589979227351836922442361796407385865272702160665422798143283183179796767671255564288, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C57_c1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C57_c1

namespace VerifiedLcalc.Certificates.Batch.C57_c2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -7, a6 := 5 },   conductor := 57,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, -1, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   geometricUpper := (3918841013586029 : Rat)/9007199254740992,   tail := (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/50875723826420520027794455673794989613675918461221180898203692932636351080332711399071641591589898383835627782144,   box := { reLo := (35305005144618055427943386262212779760265150439693968199682943164601684273597449502583860571821015961892653156397 : Rat)/84792873044034200046324092789658316022793197435368634830339488221060585133887852331786069319316497306392712970240,            reHi := (446711944261783561776710034530803438359861041877892529751137932250291620966657504592234823367693884799665299892089 : Rat)/254378619132102600138972278368974948068379592306105904491018464663181755401663556995358207957949491919178138910720,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/101751447652841040055588911347589979227351836922442361796407385865272702160665422798143283183179796767671255564288, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C57_c2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C57_c2

namespace VerifiedLcalc.Certificates.Batch.C57_c3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2, a6 := -1 },   conductor := 57,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, -1, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   geometricUpper := (3918841013586029 : Rat)/9007199254740992,   tail := (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/50875723826420520027794455673794989613675918461221180898203692932636351080332711399071641591589898383835627782144,   box := { reLo := (35305005144618055427943386262212779760265150439693968199682943164601684273597449502583860571821015961892653156397 : Rat)/84792873044034200046324092789658316022793197435368634830339488221060585133887852331786069319316497306392712970240,            reHi := (446711944261783561776710034530803438359861041877892529751137932250291620966657504592234823367693884799665299892089 : Rat)/254378619132102600138972278368974948068379592306105904491018464663181755401663556995358207957949491919178138910720,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/101751447652841040055588911347589979227351836922442361796407385865272702160665422798143283183179796767671255564288, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C57_c3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C57_c3

namespace VerifiedLcalc.Certificates.Batch.C57_c4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 8, a6 := 29 },   conductor := 57,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 1, -1, -2, 1],   alphaLo := (5397215081808807583435051761664 : Rat)/6485258397940499782562255859375,   alphaHi := (2698607540904403791726115815424 : Rat)/3242629198970249843597412109375,   geometricUpper := (3918841013586029 : Rat)/9007199254740992,   tail := (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/50875723826420520027794455673794989613675918461221180898203692932636351080332711399071641591589898383835627782144,   box := { reLo := (35305005144618055427943386262212779760265150439693968199682943164601684273597449502583860571821015961892653156397 : Rat)/84792873044034200046324092789658316022793197435368634830339488221060585133887852331786069319316497306392712970240,            reHi := (446711944261783561776710034530803438359861041877892529751137932250291620966657504592234823367693884799665299892089 : Rat)/254378619132102600138972278368974948068379592306105904491018464663181755401663556995358207957949491919178138910720,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (34079692882792921757016991807155822876039400868875113795709511390344444717624571451777636382134635896536091559909 : Rat)/101751447652841040055588911347589979227351836922442361796407385865272702160665422798143283183179796767671255564288, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C57_c4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C57_c4

namespace VerifiedLcalc.Certificates.Batch.C58_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -455, a6 := -3951 },   conductor := 58,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/6541899284688366413116455078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1635474821172091579437255859375,   geometricUpper := (3947180494134785 : Rat)/9007199254740992,   tail := (35842728450321424040304235852045868380754779398464272049363355196241303824089216669395605725963411071780710390625 : Rat)/50391461721965515109829279650464426172463760117555919802914043859603515848201063758311274237414714865440046186496,   box := { reLo := (81544600130570910409010431489820695981636076449905462782581958270094655057364101022604318361995155110260633335579 : Rat)/251957308609827575549146398252322130862318800587779599014570219298017579241005318791556371187073574327200230932480,            reHi := (87994376926757068764985681289969643260699172821100887115294151348508296839724044404089324134191142979204934146913 : Rat)/50391461721965515109829279650464426172463760117555919802914043859603515848201063758311274237414714865440046186496,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (35842728450321424040304235852045868380754779398464272049363355196241303824089216669395605725963411071780710390625 : Rat)/100782923443931030219658559300928852344927520235111839605828087719207031696402127516622548474829429730880092372992, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C58_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C58_b1

namespace VerifiedLcalc.Certificates.Batch.C58_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 5, a6 := 9 },   conductor := 58,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, -1, 1, 1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/6541899284688366413116455078125,   alphaHi := (1349303770452201895863057907712 : Rat)/1635474821172091579437255859375,   geometricUpper := (3947180494134785 : Rat)/9007199254740992,   tail := (35842728450321424040304235852045868380754779398464272049363355196241303824089216669395605725963411071780710390625 : Rat)/50391461721965515109829279650464426172463760117555919802914043859603515848201063758311274237414714865440046186496,   box := { reLo := (81544600130570910409010431489820695981636076449905462782581958270094655057364101022604318361995155110260633335579 : Rat)/251957308609827575549146398252322130862318800587779599014570219298017579241005318791556371187073574327200230932480,            reHi := (87994376926757068764985681289969643260699172821100887115294151348508296839724044404089324134191142979204934146913 : Rat)/50391461721965515109829279650464426172463760117555919802914043859603515848201063758311274237414714865440046186496,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (35842728450321424040304235852045868380754779398464272049363355196241303824089216669395605725963411071780710390625 : Rat)/100782923443931030219658559300928852344927520235111839605828087719207031696402127516622548474829429730880092372992, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C58_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C58_b2

namespace VerifiedLcalc.Certificates.Batch.C62_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -331, a6 := 2397 },   conductor := 62,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/422732578841590213775634765625,   alphaHi := (5397215081808807583452231630848 : Rat)/6763721261465443325042724609375,   geometricUpper := (4055438593140831 : Rat)/9007199254740992,   tail := (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,   box := { reLo := (10513464071516206553516516373280517838129681105524010857790426491658616705383096029186665529201611021354094675649 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,            reHi := (485735921273558365196382640467841669865125317402570658700044564873479637757359038574531391377754595487990976814651 : Rat)/242707792769413310849578548679049627468565998830422711797781444186664105199637055695161569801222963122934529392640,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/97083117107765324339831419471619850987426399532169084719112577674665642079854822278064627920489185249173811757056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C62_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C62_a1

namespace VerifiedLcalc.Certificates.Batch.C62_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -31, a6 := 5 },   conductor := 62,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/422732578841590213775634765625,   alphaHi := (5397215081808807583452231630848 : Rat)/6763721261465443325042724609375,   geometricUpper := (4055438593140831 : Rat)/9007199254740992,   tail := (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,   box := { reLo := (10513464071516206553516516373280517838129681105524010857790426491658616705383096029186665529201611021354094675649 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,            reHi := (485735921273558365196382640467841669865125317402570658700044564873479637757359038574531391377754595487990976814651 : Rat)/242707792769413310849578548679049627468565998830422711797781444186664105199637055695161569801222963122934529392640,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/97083117107765324339831419471619850987426399532169084719112577674665642079854822278064627920489185249173811757056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C62_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C62_a2

namespace VerifiedLcalc.Certificates.Batch.C62_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -21, a6 := 41 },   conductor := 62,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/422732578841590213775634765625,   alphaHi := (5397215081808807583452231630848 : Rat)/6763721261465443325042724609375,   geometricUpper := (4055438593140831 : Rat)/9007199254740992,   tail := (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,   box := { reLo := (10513464071516206553516516373280517838129681105524010857790426491658616705383096029186665529201611021354094675649 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,            reHi := (485735921273558365196382640467841669865125317402570658700044564873479637757359038574531391377754595487990976814651 : Rat)/242707792769413310849578548679049627468565998830422711797781444186664105199637055695161569801222963122934529392640,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/97083117107765324339831419471619850987426399532169084719112577674665642079854822278064627920489185249173811757056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C62_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C62_a3

namespace VerifiedLcalc.Certificates.Batch.C62_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1, a6 := 1 },   conductor := 62,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, 1, -2, 0],   alphaLo := (337325942613050473964690735104 : Rat)/422732578841590213775634765625,   alphaHi := (5397215081808807583452231630848 : Rat)/6763721261465443325042724609375,   geometricUpper := (4055438593140831 : Rat)/9007199254740992,   tail := (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,   box := { reLo := (10513464071516206553516516373280517838129681105524010857790426491658616705383096029186665529201611021354094675649 : Rat)/48541558553882662169915709735809925493713199766084542359556288837332821039927411139032313960244592624586905878528,            reHi := (485735921273558365196382640467841669865125317402570658700044564873479637757359038574531391377754595487990976814651 : Rat)/242707792769413310849578548679049627468565998830422711797781444186664105199637055695161569801222963122934529392640,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (43316860091597716266913879181257989519692576404871961695616140821394486639577007278397013572625082206819899554111 : Rat)/97083117107765324339831419471619850987426399532169084719112577674665642079854822278064627920489185249173811757056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C62_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C62_a4

namespace VerifiedLcalc.Certificates.Batch.C63_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -7056, a6 := 229905 },   conductor := 63,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6818049212622923755645751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/1704512303155730915069580078125,   geometricUpper := (2040653404829735 : Rat)/4503599627370496,   tail := (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,   box := { reLo := (308502168474897267256837294340616488467587349765528229133460612242126902428555598593024089806803115410218004141 : Rat)/1878887701284101478121408316854089536663837536508324062901254902450595765026769936766731507057040286874452623360,            reHi := (769331502909875067009113001980519921926236028906481773837271078604705703342057432510117352884510474991496282999 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/751555080513640591248563326741635814665535014603329625160501960980238306010707974706692602822816114749781049344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 7, 7] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C63_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C63_a1

namespace VerifiedLcalc.Certificates.Batch.C63_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -441, a6 := 3672 },   conductor := 63,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6818049212622923755645751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/1704512303155730915069580078125,   geometricUpper := (2040653404829735 : Rat)/4503599627370496,   tail := (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,   box := { reLo := (308502168474897267256837294340616488467587349765528229133460612242126902428555598593024089806803115410218004141 : Rat)/1878887701284101478121408316854089536663837536508324062901254902450595765026769936766731507057040286874452623360,            reHi := (769331502909875067009113001980519921926236028906481773837271078604705703342057432510117352884510474991496282999 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/751555080513640591248563326741635814665535014603329625160501960980238306010707974706692602822816114749781049344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C63_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C63_a2

namespace VerifiedLcalc.Certificates.Batch.C63_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -351, a6 := -2430 },   conductor := 63,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6818049212622923755645751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/1704512303155730915069580078125,   geometricUpper := (2040653404829735 : Rat)/4503599627370496,   tail := (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,   box := { reLo := (308502168474897267256837294340616488467587349765528229133460612242126902428555598593024089806803115410218004141 : Rat)/1878887701284101478121408316854089536663837536508324062901254902450595765026769936766731507057040286874452623360,            reHi := (769331502909875067009113001980519921926236028906481773837271078604705703342057432510117352884510474991496282999 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/751555080513640591248563326741635814665535014603329625160501960980238306010707974706692602822816114749781049344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [0, 1, 1, 0, 1, 2, 0],                kodaira := -12 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C63_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C63_a3

namespace VerifiedLcalc.Certificates.Batch.C63_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -306, a6 := 5859 },   conductor := 63,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6818049212622923755645751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/1704512303155730915069580078125,   geometricUpper := (2040653404829735 : Rat)/4503599627370496,   tail := (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,   box := { reLo := (308502168474897267256837294340616488467587349765528229133460612242126902428555598593024089806803115410218004141 : Rat)/1878887701284101478121408316854089536663837536508324062901254902450595765026769936766731507057040286874452623360,            reHi := (769331502909875067009113001980519921926236028906481773837271078604705703342057432510117352884510474991496282999 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/751555080513640591248563326741635814665535014603329625160501960980238306010707974706692602822816114749781049344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 7, 7, 7, 7, 7, 7, 7, 7] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -5 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C63_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C63_a4

namespace VerifiedLcalc.Certificates.Batch.C63_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := -36, a6 := 27 },   conductor := 63,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6818049212622923755645751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/1704512303155730915069580078125,   geometricUpper := (2040653404829735 : Rat)/4503599627370496,   tail := (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,   box := { reLo := (308502168474897267256837294340616488467587349765528229133460612242126902428555598593024089806803115410218004141 : Rat)/1878887701284101478121408316854089536663837536508324062901254902450595765026769936766731507057040286874452623360,            reHi := (769331502909875067009113001980519921926236028906481773837271078604705703342057432510117352884510474991496282999 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/751555080513640591248563326741635814665535014603329625160501960980238306010707974706692602822816114749781049344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 7, 7] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 1,                quadraticRoot := 0,                chain := [1, 2, 0],                kodaira := -8 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C63_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C63_a5

namespace VerifiedLcalc.Certificates.Batch.C63_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 0, a4 := 9, a6 := 0 },   conductor := 63,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 6,   coefficients := [1, 1, 0, -1, 2, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/6818049212622923755645751953125,   alphaHi := (1349303770452201895863057907712 : Rat)/1704512303155730915069580078125,   geometricUpper := (2040653404829735 : Rat)/4503599627370496,   tail := (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,   box := { reLo := (308502168474897267256837294340616488467587349765528229133460612242126902428555598593024089806803115410218004141 : Rat)/1878887701284101478121408316854089536663837536508324062901254902450595765026769936766731507057040286874452623360,            reHi := (769331502909875067009113001980519921926236028906481773837271078604705703342057432510117352884510474991496282999 : Rat)/375777540256820295624281663370817907332767507301664812580250980490119153005353987353346301411408057374890524672,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (353815534607447675361856412565704347564150705198051598265817050479178501473406184218132752592985280839793984375 : Rat)/751555080513640591248563326741635814665535014603329625160501960980238306010707974706692602822816114749781049344, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 7] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 1,                t := 0,                starT := 0,                cubicRoot := 2,                quadraticRoot := 0,                chain := [2],                kodaira := -6 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C63_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C63_a6
