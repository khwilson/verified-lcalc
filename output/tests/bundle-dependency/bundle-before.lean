module
public import VerifiedLcalc.Assumptions.Batch
public import VerifiedLcalc.Assumptions.FastSign
public import VerifiedLcalc.Assumptions.TameCertification
public import VerifiedLcalc.Assumptions.WildCertification

@[expose] public section

namespace VerifiedLcalc.Certificates.Batch.C11_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -7820, a6 := -263580 },   conductor := 11,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 1,   coefficients := [1],   alphaLo := (5397215081808807583435051761664 : Rat)/2848959001535859775543212890625,   alphaHi := (337325942613050473965764476928 : Rat)/178059937595991230010986328125,   geometricUpper := (169336229459221 : Rat)/1125899906842624,   tail := (28674758607465946046101926841 : Rat)/104834424879811077321286221824,   box := { reLo := (366028917649787835048376743221 : Rat)/13418806384615817897124636393472,            reHi := (963345890145134125303004031503 : Rat)/1677350798076977237140579549184,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (28674758607465946046101926841 : Rat)/209668849759622154642572443648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C11_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C11_a1

namespace VerifiedLcalc.Certificates.Batch.C11_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := -10, a6 := -20 },   conductor := 11,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 1,   coefficients := [1],   alphaLo := (5397215081808807583435051761664 : Rat)/2848959001535859775543212890625,   alphaHi := (337325942613050473965764476928 : Rat)/178059937595991230010986328125,   geometricUpper := (169336229459221 : Rat)/1125899906842624,   tail := (28674758607465946046101926841 : Rat)/104834424879811077321286221824,   box := { reLo := (366028917649787835048376743221 : Rat)/13418806384615817897124636393472,            reHi := (963345890145134125303004031503 : Rat)/1677350798076977237140579549184,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (28674758607465946046101926841 : Rat)/209668849759622154642572443648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C11_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C11_a2

namespace VerifiedLcalc.Certificates.Batch.C11_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 1, a4 := 0, a6 := 0 },   conductor := 11,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 1,   coefficients := [1],   alphaLo := (5397215081808807583435051761664 : Rat)/2848959001535859775543212890625,   alphaHi := (337325942613050473965764476928 : Rat)/178059937595991230010986328125,   geometricUpper := (169336229459221 : Rat)/1125899906842624,   tail := (28674758607465946046101926841 : Rat)/104834424879811077321286221824,   box := { reLo := (366028917649787835048376743221 : Rat)/13418806384615817897124636393472,            reHi := (963345890145134125303004031503 : Rat)/1677350798076977237140579549184,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (28674758607465946046101926841 : Rat)/209668849759622154642572443648, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C11_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C11_a3

namespace VerifiedLcalc.Certificates.Batch.C14_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -2731, a6 := -55146 },   conductor := 14,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3214059221806180286407470703125,   alphaHi := (1349303770452201895863057907712 : Rat)/803514805451545047760009765625,   geometricUpper := (839981917505001 : Rat)/4503599627370496,   tail := (16001974542561155106121813713613888837342905027 : Rat)/91584159005113008701027154246158944241113366528,   box := { reLo := (14975418234595341917150284157885108460203621693 : Rat)/91584159005113008701027154246158944241113366528,            reHi := (46979367319717682633046517107462481045965423299 : Rat)/91584159005113008701027154246158944241113366528,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16001974542561155106121813713613888837342905027 : Rat)/183168318010226017402054308492317888482226733056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C14_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C14_a1

namespace VerifiedLcalc.Certificates.Batch.C14_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -171, a6 := -874 },   conductor := 14,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3214059221806180286407470703125,   alphaHi := (1349303770452201895863057907712 : Rat)/803514805451545047760009765625,   geometricUpper := (839981917505001 : Rat)/4503599627370496,   tail := (16001974542561155106121813713613888837342905027 : Rat)/91584159005113008701027154246158944241113366528,   box := { reLo := (14975418234595341917150284157885108460203621693 : Rat)/91584159005113008701027154246158944241113366528,            reHi := (46979367319717682633046517107462481045965423299 : Rat)/91584159005113008701027154246158944241113366528,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16001974542561155106121813713613888837342905027 : Rat)/183168318010226017402054308492317888482226733056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C14_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C14_a2

namespace VerifiedLcalc.Certificates.Batch.C14_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -36, a6 := -70 },   conductor := 14,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3214059221806180286407470703125,   alphaHi := (1349303770452201895863057907712 : Rat)/803514805451545047760009765625,   geometricUpper := (839981917505001 : Rat)/4503599627370496,   tail := (16001974542561155106121813713613888837342905027 : Rat)/91584159005113008701027154246158944241113366528,   box := { reLo := (14975418234595341917150284157885108460203621693 : Rat)/91584159005113008701027154246158944241113366528,            reHi := (46979367319717682633046517107462481045965423299 : Rat)/91584159005113008701027154246158944241113366528,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16001974542561155106121813713613888837342905027 : Rat)/183168318010226017402054308492317888482226733056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C14_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C14_a3

namespace VerifiedLcalc.Certificates.Batch.C14_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -11, a6 := 12 },   conductor := 14,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3214059221806180286407470703125,   alphaHi := (1349303770452201895863057907712 : Rat)/803514805451545047760009765625,   geometricUpper := (839981917505001 : Rat)/4503599627370496,   tail := (16001974542561155106121813713613888837342905027 : Rat)/91584159005113008701027154246158944241113366528,   box := { reLo := (14975418234595341917150284157885108460203621693 : Rat)/91584159005113008701027154246158944241113366528,            reHi := (46979367319717682633046517107462481045965423299 : Rat)/91584159005113008701027154246158944241113366528,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16001974542561155106121813713613888837342905027 : Rat)/183168318010226017402054308492317888482226733056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C14_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C14_a4

namespace VerifiedLcalc.Certificates.Batch.C14_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -1, a6 := 0 },   conductor := 14,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3214059221806180286407470703125,   alphaHi := (1349303770452201895863057907712 : Rat)/803514805451545047760009765625,   geometricUpper := (839981917505001 : Rat)/4503599627370496,   tail := (16001974542561155106121813713613888837342905027 : Rat)/91584159005113008701027154246158944241113366528,   box := { reLo := (14975418234595341917150284157885108460203621693 : Rat)/91584159005113008701027154246158944241113366528,            reHi := (46979367319717682633046517107462481045965423299 : Rat)/91584159005113008701027154246158944241113366528,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16001974542561155106121813713613888837342905027 : Rat)/183168318010226017402054308492317888482226733056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C14_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C14_a5

namespace VerifiedLcalc.Certificates.Batch.C14_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 4, a6 := -6 },   conductor := 14,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3214059221806180286407470703125,   alphaHi := (1349303770452201895863057907712 : Rat)/803514805451545047760009765625,   geometricUpper := (839981917505001 : Rat)/4503599627370496,   tail := (16001974542561155106121813713613888837342905027 : Rat)/91584159005113008701027154246158944241113366528,   box := { reLo := (14975418234595341917150284157885108460203621693 : Rat)/91584159005113008701027154246158944241113366528,            reHi := (46979367319717682633046517107462481045965423299 : Rat)/91584159005113008701027154246158944241113366528,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (16001974542561155106121813713613888837342905027 : Rat)/183168318010226017402054308492317888482226733056, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C14_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C14_a6

namespace VerifiedLcalc.Certificates.Batch.C15_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -2160, a6 := -39540 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a1

namespace VerifiedLcalc.Certificates.Batch.C15_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -135, a6 := -660 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a2

namespace VerifiedLcalc.Certificates.Batch.C15_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -110, a6 := -880 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a3

namespace VerifiedLcalc.Certificates.Batch.C15_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -80, a6 := 242 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a4

namespace VerifiedLcalc.Certificates.Batch.C15_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -10, a6 := -10 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a5

namespace VerifiedLcalc.Certificates.Batch.C15_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := -5, a6 := 2 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a6

namespace VerifiedLcalc.Certificates.Batch.C15_a7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 0, a6 := 0 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a7.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a7

namespace VerifiedLcalc.Certificates.Batch.C15_a8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 1, a3 := 1, a4 := 35, a6 := -28 },   conductor := 15,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (5397215081808807583435051761664 : Rat)/3326867361982700252532958984375,   alphaHi := (2698607540904403791726115815424 : Rat)/1663433680991350078582763671875,   geometricUpper := (889198773535397 : Rat)/4503599627370496,   tail := (56948407485583559009830130385912563634952277613 : Rat)/266766585548039462425261726799709113237054160896,   box := { reLo := (37993905717531698412133225703610615311290003859 : Rat)/266766585548039462425261726799709113237054160896,            reHi := (151890720688698934899955676903413729359424982637 : Rat)/266766585548039462425261726799709113237054160896,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (56948407485583559009830130385912563634952277613 : Rat)/533533171096078924850523453599418226474108321792, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C15_a8.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C15_a8

namespace VerifiedLcalc.Certificates.Batch.C17_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -91, a6 := -310 },   conductor := 17,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (674651885226100947929381470208 : Rat)/442715095499536800384521484375,   alphaHi := (5397215081808807583452231630848 : Rat)/3541720763996294307708740234375,   geometricUpper := (1962320887651377 : Rat)/9007199254740992,   tail := (204020517183498880191308444551785699844451030091 : Rat)/671586537148613887684767354558265101892634804224,   box := { reLo := (56729123702370028899078315498072767483282893749 : Rat)/671586537148613887684767354558265101892634804224,            reHi := (464770158069368012964946175802393352980090934347 : Rat)/671586537148613887684767354558265101892634804224,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (204020517183498880191308444551785699844451030091 : Rat)/1343173074297227775369534709116530203785269608448, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C17_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C17_a1

namespace VerifiedLcalc.Certificates.Batch.C17_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -6, a6 := -4 },   conductor := 17,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (674651885226100947929381470208 : Rat)/442715095499536800384521484375,   alphaHi := (5397215081808807583452231630848 : Rat)/3541720763996294307708740234375,   geometricUpper := (1962320887651377 : Rat)/9007199254740992,   tail := (204020517183498880191308444551785699844451030091 : Rat)/671586537148613887684767354558265101892634804224,   box := { reLo := (56729123702370028899078315498072767483282893749 : Rat)/671586537148613887684767354558265101892634804224,            reHi := (464770158069368012964946175802393352980090934347 : Rat)/671586537148613887684767354558265101892634804224,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (204020517183498880191308444551785699844451030091 : Rat)/1343173074297227775369534709116530203785269608448, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C17_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C17_a2

namespace VerifiedLcalc.Certificates.Batch.C17_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1, a6 := -14 },   conductor := 17,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (674651885226100947929381470208 : Rat)/442715095499536800384521484375,   alphaHi := (5397215081808807583452231630848 : Rat)/3541720763996294307708740234375,   geometricUpper := (1962320887651377 : Rat)/9007199254740992,   tail := (204020517183498880191308444551785699844451030091 : Rat)/671586537148613887684767354558265101892634804224,   box := { reLo := (56729123702370028899078315498072767483282893749 : Rat)/671586537148613887684767354558265101892634804224,            reHi := (464770158069368012964946175802393352980090934347 : Rat)/671586537148613887684767354558265101892634804224,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (204020517183498880191308444551785699844451030091 : Rat)/1343173074297227775369534709116530203785269608448, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C17_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C17_a3

namespace VerifiedLcalc.Certificates.Batch.C17_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -1, a6 := 0 },   conductor := 17,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, -1],   alphaLo := (674651885226100947929381470208 : Rat)/442715095499536800384521484375,   alphaHi := (5397215081808807583452231630848 : Rat)/3541720763996294307708740234375,   geometricUpper := (1962320887651377 : Rat)/9007199254740992,   tail := (204020517183498880191308444551785699844451030091 : Rat)/671586537148613887684767354558265101892634804224,   box := { reLo := (56729123702370028899078315498072767483282893749 : Rat)/671586537148613887684767354558265101892634804224,            reHi := (464770158069368012964946175802393352980090934347 : Rat)/671586537148613887684767354558265101892634804224,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (204020517183498880191308444551785699844451030091 : Rat)/1343173074297227775369534709116530203785269608448, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C17_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C17_a4

namespace VerifiedLcalc.Certificates.Batch.C19_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -769, a6 := -8470 },   conductor := 19,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3744265681815228748321533203125,   alphaHi := (1349303770452201895863057907712 : Rat)/936066420453807163238525390625,   geometricUpper := (1065469370893833 : Rat)/4503599627370496,   tail := (32657781031117644621850685996574299256386294499 : Rat)/79388348631468729890098135011174997656334237696,   box := { reLo := (4905883979689765869456709142333794267737287965 : Rat)/79388348631468729890098135011174997656334237696,            reHi := (70221446041925090368667096185730488947743462115 : Rat)/79388348631468729890098135011174997656334237696,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (32657781031117644621850685996574299256386294499 : Rat)/158776697262937459780196270022349995312668475392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C19_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C19_a1

namespace VerifiedLcalc.Certificates.Batch.C19_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := -9, a6 := -15 },   conductor := 19,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3744265681815228748321533203125,   alphaHi := (1349303770452201895863057907712 : Rat)/936066420453807163238525390625,   geometricUpper := (1065469370893833 : Rat)/4503599627370496,   tail := (32657781031117644621850685996574299256386294499 : Rat)/79388348631468729890098135011174997656334237696,   box := { reLo := (4905883979689765869456709142333794267737287965 : Rat)/79388348631468729890098135011174997656334237696,            reHi := (70221446041925090368667096185730488947743462115 : Rat)/79388348631468729890098135011174997656334237696,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (32657781031117644621850685996574299256386294499 : Rat)/158776697262937459780196270022349995312668475392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C19_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C19_a2

namespace VerifiedLcalc.Certificates.Batch.C19_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 1, a4 := 1, a6 := 0 },   conductor := 19,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3744265681815228748321533203125,   alphaHi := (1349303770452201895863057907712 : Rat)/936066420453807163238525390625,   geometricUpper := (1065469370893833 : Rat)/4503599627370496,   tail := (32657781031117644621850685996574299256386294499 : Rat)/79388348631468729890098135011174997656334237696,   box := { reLo := (4905883979689765869456709142333794267737287965 : Rat)/79388348631468729890098135011174997656334237696,            reHi := (70221446041925090368667096185730488947743462115 : Rat)/79388348631468729890098135011174997656334237696,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (32657781031117644621850685996574299256386294499 : Rat)/158776697262937459780196270022349995312668475392, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C19_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C19_a3

namespace VerifiedLcalc.Certificates.Batch.C20_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -41, a6 := -116 },   conductor := 20,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3841535533997784328460693359375,   alphaHi := (2698607540904403791726115815424 : Rat)/1920767766998892116546630859375,   geometricUpper := (2210151861010583 : Rat)/9007199254740992,   tail := (874482987545058747846631253892387394862127848247 : Rat)/1853908113393262429187694968852611532269499187200,   box := { reLo := (35326677163320832748485236106603169079105610953 : Rat)/1853908113393262429187694968852611532269499187200,            reHi := (1784292652253439151742336955325577075036304513847 : Rat)/1853908113393262429187694968852611532269499187200,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (874482987545058747846631253892387394862127848247 : Rat)/3707816226786524858375389937705223064538998374400, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C20_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C20_a1

namespace VerifiedLcalc.Certificates.Batch.C20_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -36, a6 := -140 },   conductor := 20,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3841535533997784328460693359375,   alphaHi := (2698607540904403791726115815424 : Rat)/1920767766998892116546630859375,   geometricUpper := (2210151861010583 : Rat)/9007199254740992,   tail := (874482987545058747846631253892387394862127848247 : Rat)/1853908113393262429187694968852611532269499187200,   box := { reLo := (35326677163320832748485236106603169079105610953 : Rat)/1853908113393262429187694968852611532269499187200,            reHi := (1784292652253439151742336955325577075036304513847 : Rat)/1853908113393262429187694968852611532269499187200,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (874482987545058747846631253892387394862127848247 : Rat)/3707816226786524858375389937705223064538998374400, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C20_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C20_a2

namespace VerifiedLcalc.Certificates.Batch.C20_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := -1, a6 := 0 },   conductor := 20,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3841535533997784328460693359375,   alphaHi := (2698607540904403791726115815424 : Rat)/1920767766998892116546630859375,   geometricUpper := (2210151861010583 : Rat)/9007199254740992,   tail := (874482987545058747846631253892387394862127848247 : Rat)/1853908113393262429187694968852611532269499187200,   box := { reLo := (35326677163320832748485236106603169079105610953 : Rat)/1853908113393262429187694968852611532269499187200,            reHi := (1784292652253439151742336955325577075036304513847 : Rat)/1853908113393262429187694968852611532269499187200,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (874482987545058747846631253892387394862127848247 : Rat)/3707816226786524858375389937705223064538998374400, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C20_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C20_a3

namespace VerifiedLcalc.Certificates.Batch.C20_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 1, a3 := 0, a4 := 4, a6 := 4 },   conductor := 20,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 2,   coefficients := [1, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/3841535533997784328460693359375,   alphaHi := (2698607540904403791726115815424 : Rat)/1920767766998892116546630859375,   geometricUpper := (2210151861010583 : Rat)/9007199254740992,   tail := (874482987545058747846631253892387394862127848247 : Rat)/1853908113393262429187694968852611532269499187200,   box := { reLo := (35326677163320832748485236106603169079105610953 : Rat)/1853908113393262429187694968852611532269499187200,            reHi := (1784292652253439151742336955325577075036304513847 : Rat)/1853908113393262429187694968852611532269499187200,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (874482987545058747846631253892387394862127848247 : Rat)/3707816226786524858375389937705223064538998374400, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 5, 5] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -4 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C20_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C20_a4

namespace VerifiedLcalc.Certificates.Batch.C21_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -784, a6 := -8515 },   conductor := 21,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/3936402548255960941314697265625,   geometricUpper := (2286267861052585 : Rat)/9007199254740992,   tail := (27321745737796267726573286323950996870280452596265033955950625 : Rat)/124111306425273454790874028318542349105562305626594033038000128,   box := { reLo := (87121948401832985296573664271691264996393690339895155313950621 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            reHi := (251052422828610743226366392826789199063994313935226403982852195 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (27321745737796267726573286323950996870280452596265033955950625 : Rat)/248222612850546909581748056637084698211124611253188066076000256, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C21_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C21_a1

namespace VerifiedLcalc.Certificates.Batch.C21_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -49, a6 := -136 },   conductor := 21,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/3936402548255960941314697265625,   geometricUpper := (2286267861052585 : Rat)/9007199254740992,   tail := (27321745737796267726573286323950996870280452596265033955950625 : Rat)/124111306425273454790874028318542349105562305626594033038000128,   box := { reLo := (87121948401832985296573664271691264996393690339895155313950621 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            reHi := (251052422828610743226366392826789199063994313935226403982852195 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (27321745737796267726573286323950996870280452596265033955950625 : Rat)/248222612850546909581748056637084698211124611253188066076000256, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C21_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C21_a2

namespace VerifiedLcalc.Certificates.Batch.C21_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -39, a6 := 90 },   conductor := 21,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/3936402548255960941314697265625,   geometricUpper := (2286267861052585 : Rat)/9007199254740992,   tail := (27321745737796267726573286323950996870280452596265033955950625 : Rat)/124111306425273454790874028318542349105562305626594033038000128,   box := { reLo := (87121948401832985296573664271691264996393690339895155313950621 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            reHi := (251052422828610743226366392826789199063994313935226403982852195 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (27321745737796267726573286323950996870280452596265033955950625 : Rat)/248222612850546909581748056637084698211124611253188066076000256, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C21_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C21_a3

namespace VerifiedLcalc.Certificates.Batch.C21_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -34, a6 := -217 },   conductor := 21,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/3936402548255960941314697265625,   geometricUpper := (2286267861052585 : Rat)/9007199254740992,   tail := (27321745737796267726573286323950996870280452596265033955950625 : Rat)/124111306425273454790874028318542349105562305626594033038000128,   box := { reLo := (87121948401832985296573664271691264996393690339895155313950621 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            reHi := (251052422828610743226366392826789199063994313935226403982852195 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (27321745737796267726573286323950996870280452596265033955950625 : Rat)/248222612850546909581748056637084698211124611253188066076000256, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C21_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C21_a4

namespace VerifiedLcalc.Certificates.Batch.C21_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := -4, a6 := -1 },   conductor := 21,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/3936402548255960941314697265625,   geometricUpper := (2286267861052585 : Rat)/9007199254740992,   tail := (27321745737796267726573286323950996870280452596265033955950625 : Rat)/124111306425273454790874028318542349105562305626594033038000128,   box := { reLo := (87121948401832985296573664271691264996393690339895155313950621 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            reHi := (251052422828610743226366392826789199063994313935226403982852195 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (27321745737796267726573286323950996870280452596265033955950625 : Rat)/248222612850546909581748056637084698211124611253188066076000256, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C21_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C21_a5

namespace VerifiedLcalc.Certificates.Batch.C21_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 0, a4 := 1, a6 := 0 },   conductor := 21,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (2698607540904403791717525880832 : Rat)/1968201274127980518341064453125,   alphaHi := (5397215081808807583452231630848 : Rat)/3936402548255960941314697265625,   geometricUpper := (2286267861052585 : Rat)/9007199254740992,   tail := (27321745737796267726573286323950996870280452596265033955950625 : Rat)/124111306425273454790874028318542349105562305626594033038000128,   box := { reLo := (87121948401832985296573664271691264996393690339895155313950621 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            reHi := (251052422828610743226366392826789199063994313935226403982852195 : Rat)/372333919275820364372622084955627047316686916879782099114000384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (27321745737796267726573286323950996870280452596265033955950625 : Rat)/248222612850546909581748056637084698211124611253188066076000256, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C21_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C21_a6

namespace VerifiedLcalc.Certificates.Batch.C24_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -384, a6 := -2772 },   conductor := 24,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1052047833714120197296142578125,   alphaHi := (5397215081808807583452231630848 : Rat)/4208191334856480693817138671875,   geometricUpper := (2497959864709543 : Rat)/9007199254740992,   tail := (38935147540150355448664989879993606913819437813320800269784801 : Rat)/116557883330681081616784220614546102438631724794499424822755328,   box := { reLo := (24057235897484009936363514192472422409022232013392062322288927 : Rat)/116557883330681081616784220614546102438631724794499424822755328,            reHi := (305782592933354266025277102093271320139469673066170662674564259 : Rat)/349673649992043244850352661843638307315895174383498274468265984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (38935147540150355448664989879993606913819437813320800269784801 : Rat)/233115766661362163233568441229092204877263449588998849645510656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C24_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C24_a1

namespace VerifiedLcalc.Certificates.Batch.C24_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -64, a6 := 220 },   conductor := 24,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1052047833714120197296142578125,   alphaHi := (5397215081808807583452231630848 : Rat)/4208191334856480693817138671875,   geometricUpper := (2497959864709543 : Rat)/9007199254740992,   tail := (38935147540150355448664989879993606913819437813320800269784801 : Rat)/116557883330681081616784220614546102438631724794499424822755328,   box := { reLo := (24057235897484009936363514192472422409022232013392062322288927 : Rat)/116557883330681081616784220614546102438631724794499424822755328,            reHi := (305782592933354266025277102093271320139469673066170662674564259 : Rat)/349673649992043244850352661843638307315895174383498274468265984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (38935147540150355448664989879993606913819437813320800269784801 : Rat)/233115766661362163233568441229092204877263449588998849645510656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 1, chain := [], kodaira := -3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C24_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C24_a2

namespace VerifiedLcalc.Certificates.Batch.C24_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -24, a6 := -36 },   conductor := 24,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1052047833714120197296142578125,   alphaHi := (5397215081808807583452231630848 : Rat)/4208191334856480693817138671875,   geometricUpper := (2497959864709543 : Rat)/9007199254740992,   tail := (38935147540150355448664989879993606913819437813320800269784801 : Rat)/116557883330681081616784220614546102438631724794499424822755328,   box := { reLo := (24057235897484009936363514192472422409022232013392062322288927 : Rat)/116557883330681081616784220614546102438631724794499424822755328,            reHi := (305782592933354266025277102093271320139469673066170662674564259 : Rat)/349673649992043244850352661843638307315895174383498274468265984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (38935147540150355448664989879993606913819437813320800269784801 : Rat)/233115766661362163233568441229092204877263449588998849645510656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C24_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C24_a3

namespace VerifiedLcalc.Certificates.Batch.C24_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := -4, a6 := 4 },   conductor := 24,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1052047833714120197296142578125,   alphaHi := (5397215081808807583452231630848 : Rat)/4208191334856480693817138671875,   geometricUpper := (2497959864709543 : Rat)/9007199254740992,   tail := (38935147540150355448664989879993606913819437813320800269784801 : Rat)/116557883330681081616784220614546102438631724794499424822755328,   box := { reLo := (24057235897484009936363514192472422409022232013392062322288927 : Rat)/116557883330681081616784220614546102438631724794499424822755328,            reHi := (305782592933354266025277102093271320139469673066170662674564259 : Rat)/349673649992043244850352661843638307315895174383498274468265984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (38935147540150355448664989879993606913819437813320800269784801 : Rat)/233115766661362163233568441229092204877263449588998849645510656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := -5 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C24_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C24_a4

namespace VerifiedLcalc.Certificates.Batch.C24_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 1, a6 := 0 },   conductor := 24,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1052047833714120197296142578125,   alphaHi := (5397215081808807583452231630848 : Rat)/4208191334856480693817138671875,   geometricUpper := (2497959864709543 : Rat)/9007199254740992,   tail := (38935147540150355448664989879993606913819437813320800269784801 : Rat)/116557883330681081616784220614546102438631724794499424822755328,   box := { reLo := (24057235897484009936363514192472422409022232013392062322288927 : Rat)/116557883330681081616784220614546102438631724794499424822755328,            reHi := (305782592933354266025277102093271320139469673066170662674564259 : Rat)/349673649992043244850352661843638307315895174383498274468265984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (38935147540150355448664989879993606913819437813320800269784801 : Rat)/233115766661362163233568441229092204877263449588998849645510656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 1, s := 0, t := 1, starT := 0, cubicRoot := 0, quadraticRoot := 0, chain := [], kodaira := 3 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C24_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C24_a5

namespace VerifiedLcalc.Certificates.Batch.C24_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := -1, a3 := 0, a4 := 16, a6 := -180 },   conductor := 24,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, -1],   alphaLo := (1349303770452201895858762940416 : Rat)/1052047833714120197296142578125,   alphaHi := (5397215081808807583452231630848 : Rat)/4208191334856480693817138671875,   geometricUpper := (2497959864709543 : Rat)/9007199254740992,   tail := (38935147540150355448664989879993606913819437813320800269784801 : Rat)/116557883330681081616784220614546102438631724794499424822755328,   box := { reLo := (24057235897484009936363514192472422409022232013392062322288927 : Rat)/116557883330681081616784220614546102438631724794499424822755328,            reHi := (305782592933354266025277102093271320139469673066170662674564259 : Rat)/349673649992043244850352661843638307315895174383498274468265984,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (38935147540150355448664989879993606913819437813320800269784801 : Rat)/233115766661362163233568441229092204877263449588998849645510656, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := some { r := 0, s := 1, t := 0, starT := 1, cubicRoot := 1, quadraticRoot := 0, chain := [], kodaira := -2 },   atThree := none }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C24_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C24_a6

namespace VerifiedLcalc.Certificates.Batch.C26_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -460, a6 := -3830 },   conductor := 26,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1095006102627341938018798828125,   alphaHi := (5397215081808807583452231630848 : Rat)/4380024410509367656707763671875,   geometricUpper := (1313431233851677 : Rat)/4503599627370496,   tail := (2975975551220919135183277187037875167942493592025536842604241 : Rat)/6997405297688334622436785240789524108272837301649980530884608,   box := { reLo := (626032321604541268564814314022782190830259844610415077450031 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            reHi := (2192661141348794647061212453475343643776871699767156830429083 : Rat)/2332468432562778207478928413596508036090945767216660176961536,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2975975551220919135183277187037875167942493592025536842604241 : Rat)/13994810595376669244873570481579048216545674603299961061769216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C26_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C26_a1

namespace VerifiedLcalc.Certificates.Batch.C26_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -5, a6 := -8 },   conductor := 26,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1095006102627341938018798828125,   alphaHi := (5397215081808807583452231630848 : Rat)/4380024410509367656707763671875,   geometricUpper := (1313431233851677 : Rat)/4503599627370496,   tail := (2975975551220919135183277187037875167942493592025536842604241 : Rat)/6997405297688334622436785240789524108272837301649980530884608,   box := { reLo := (626032321604541268564814314022782190830259844610415077450031 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            reHi := (2192661141348794647061212453475343643776871699767156830429083 : Rat)/2332468432562778207478928413596508036090945767216660176961536,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2975975551220919135183277187037875167942493592025536842604241 : Rat)/13994810595376669244873570481579048216545674603299961061769216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C26_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C26_a2

namespace VerifiedLcalc.Certificates.Batch.C26_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 0, a6 := 0 },   conductor := 26,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, -1, 1],   alphaLo := (1349303770452201895858762940416 : Rat)/1095006102627341938018798828125,   alphaHi := (5397215081808807583452231630848 : Rat)/4380024410509367656707763671875,   geometricUpper := (1313431233851677 : Rat)/4503599627370496,   tail := (2975975551220919135183277187037875167942493592025536842604241 : Rat)/6997405297688334622436785240789524108272837301649980530884608,   box := { reLo := (626032321604541268564814314022782190830259844610415077450031 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            reHi := (2192661141348794647061212453475343643776871699767156830429083 : Rat)/2332468432562778207478928413596508036090945767216660176961536,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2975975551220919135183277187037875167942493592025536842604241 : Rat)/13994810595376669244873570481579048216545674603299961061769216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C26_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C26_a3

namespace VerifiedLcalc.Certificates.Batch.C26_b1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -213, a6 := -1257 },   conductor := 26,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 1, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/1095006102627341938018798828125,   alphaHi := (5397215081808807583452231630848 : Rat)/4380024410509367656707763671875,   geometricUpper := (1313431233851677 : Rat)/4503599627370496,   tail := (2975975551220919135183277187037875167942493592025536842604241 : Rat)/6997405297688334622436785240789524108272837301649980530884608,   box := { reLo := (1353489276436672568602940606648491939605325676573679418695983 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            reHi := (7305440378878516277045826870069975598838708712591789356916433 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2975975551220919135183277187037875167942493592025536842604241 : Rat)/13994810595376669244873570481579048216545674603299961061769216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C26_b1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C26_b1

namespace VerifiedLcalc.Certificates.Batch.C26_b2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := -1, a3 := 1, a4 := -3, a6 := 3 },   conductor := 26,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 1, -3],   alphaLo := (1349303770452201895858762940416 : Rat)/1095006102627341938018798828125,   alphaHi := (5397215081808807583452231630848 : Rat)/4380024410509367656707763671875,   geometricUpper := (1313431233851677 : Rat)/4503599627370496,   tail := (2975975551220919135183277187037875167942493592025536842604241 : Rat)/6997405297688334622436785240789524108272837301649980530884608,   box := { reLo := (1353489276436672568602940606648491939605325676573679418695983 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            reHi := (7305440378878516277045826870069975598838708712591789356916433 : Rat)/6997405297688334622436785240789524108272837301649980530884608,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (2975975551220919135183277187037875167942493592025536842604241 : Rat)/13994810595376669244873570481579048216545674603299961061769216, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C26_b2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C26_b2

namespace VerifiedLcalc.Certificates.Batch.C27_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -270, a6 := -1708 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 1,                chain := [],                kodaira := -2 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C27_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C27_a1

namespace VerifiedLcalc.Certificates.Batch.C27_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := -30, a6 := 63 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 4 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C27_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C27_a2

namespace VerifiedLcalc.Certificates.Batch.C27_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := -7 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3, 3, 3, 3, 3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 0,                s := 0,                t := 1,                starT := 1,                cubicRoot := 1,                quadraticRoot := 0,                chain := [],                kodaira := -4 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C27_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C27_a3

namespace VerifiedLcalc.Certificates.Batch.C27_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 0, a2 := 0, a3 := 1, a4 := 0, a6 := 0 },   conductor := 27,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 3,   coefficients := [1, 0, 0],   alphaLo := (5397215081808807583435051761664 : Rat)/4463460944111230373382568359375,   alphaHi := (2698607540904403791726115815424 : Rat)/2231730472055615139007568359375,   geometricUpper := (1344036524972249 : Rat)/4503599627370496,   tail := (3263204448332309215479501370303288585362349316711514364236001 : Rat)/6860901137886989033689731413179591094646139878553955187294208,   box := { reLo := (831876147865264528075836514639715100111871186526941864210207 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            reHi := (7358285044529886005887004438874754185972352322640910268027105 : Rat)/6860901137886989033689731413179591094646139878553955187294208,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (3263204448332309215479501370303288585362349316711514364236001 : Rat)/13721802275773978067379462826359182189292279757107910374588416, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifyWildCentralModel result nonsingular
    ({ primes := [3, 3, 3] }) (by decide +kernel)
    ({ atTwo := none,   atThree := some { r := 2,                s := 0,                t := 1,                starT := 0,                cubicRoot := 0,                quadraticRoot := 0,                chain := [],                kodaira := 2 } }) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) payload_correct (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C27_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C27_a4

namespace VerifiedLcalc.Certificates.Batch.C30_a1
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -5334, a6 := -150368 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a1.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a1

namespace VerifiedLcalc.Certificates.Batch.C30_a2
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -454, a6 := -544 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a2.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a2

namespace VerifiedLcalc.Certificates.Batch.C30_a3
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -334, a6 := -2368 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a3.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a3

namespace VerifiedLcalc.Certificates.Batch.C30_a4
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -289, a6 := 1862 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a4.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a4

namespace VerifiedLcalc.Certificates.Batch.C30_a5
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -69, a6 := -194 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a5.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a5

namespace VerifiedLcalc.Certificates.Batch.C30_a6
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -19, a6 := 26 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a6.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a6

namespace VerifiedLcalc.Certificates.Batch.C30_a7
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := -14, a6 := -64 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a7.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a7

namespace VerifiedLcalc.Certificates.Batch.C30_a8
open VerifiedLcalc VerifiedLcalc.EllipticCurve VerifiedLcalc.Assumptions

def result : CentralResult :=
  { equation := { a1 := 1, a2 := 0, a3 := 1, a4 := 1, a6 := 2 },   conductor := 30,   rootNumber := 1,   policy := { precisionBits := 53 },   termLimit := 4,   coefficients := [1, -1, 1, 1],   alphaLo := (674651885226100947929381470208 : Rat)/588112617941541957855224609375,   alphaHi := (5397215081808807583452231630848 : Rat)/4704900943532335567474365234375,   geometricUpper := (715039403323985 : Rat)/2251799813685248,   tail := (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,   box := { reLo := (62040682480058812304004544683230803442370538870551455776959796351353993717913 : Rat)/235668983924222998313971135605309920438530730529238485616337993563636500529152,            reHi := (67409592896647938228479840221030401845034568834081747454984725321060377987021 : Rat)/78556327974740999437990378535103306812843576843079495205445997854545500176384,            imLo := 0,            imHi := 0 } }

theorem payload_correct : CentralPayloadCorrect result := by
  unfold CentralPayloadCorrect
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    (23364682701647482227104986087737100786035235444408390291364468753298342578125 : Rat)/157112655949481998875980757070206613625687153686158990410891995709091000352768, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem nonsingular : discriminant result.equation ≠ 0 := by decide +kernel

theorem analytic_rank_zero : analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = 0 :=
  certifySemistableCentralModel result nonsingular (by decide +kernel)
    (by decide +kernel) (semistableSign_eq_fast result.equation |>.trans (by decide +kernel)) payload_correct
    (by decide +kernel)

def certifiedRank : {n : ℕ // analyticOrderAt (modularWitness result.equation nonsingular).formL (1 : ℂ) = n} :=
  ⟨0, analytic_rank_zero⟩

set_option pp.fullNames true

/-- info: 'VerifiedLcalc.Certificates.Batch.C30_a8.analytic_rank_zero' depends on axioms: [propext, Classical.choice, Quot.sound, VerifiedLcalc.Assumptions.ellipticModularity] -/
#guard_msgs (whitespace := lax) in
#print axioms analytic_rank_zero

end VerifiedLcalc.Certificates.Batch.C30_a8
