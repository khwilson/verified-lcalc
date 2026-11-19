module
public import VerifiedLcalc.EllipticCurve.Tate.WildArithmetic
@[expose] public section
namespace VerifiedLcalc.EllipticCurve.WildExamples
set_option maxRecDepth 100000
namespace C27_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -270, a₆ := -1708 }
def data : WildData := (wildData? equation).getD ⟨none, none⟩
theorem valid : data.Valid equation := by decide +kernel
theorem products : wildLevelFast equation data = 27 ∧ wildSignFast equation data = 1 := by decide +kernel
def wrongKodaira : WildData := {data with atThree := data.atThree.map (fun w => {w with kodaira := 3})}
theorem wrong_kodaira_rejected : ¬ wrongKodaira.Valid equation := by decide +kernel
end C27_a1
namespace C32_a4
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 4, a₆ := 0 }
def data : WildData := (wildData? equation).getD ⟨none, none⟩
theorem valid : data.Valid equation := by decide +kernel
theorem products : wildLevelFast equation data = 32 ∧ wildSignFast equation data = 1 := by decide +kernel
def shortenedChain : WildData := {data with atTwo := data.atTwo.map (fun w => {w with chain := w.chain.tail})}
theorem shortened_chain_rejected : ¬ shortenedChain.Valid equation := by decide +kernel
end C32_a4
namespace C36_a1
def equation : (WeierstrassCurve ℤ) := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -135, a₆ := -594 }
def data : WildData := (wildData? equation).getD ⟨none, none⟩
theorem valid : data.Valid equation := by decide +kernel
theorem products : wildLevelFast equation data = 36 ∧ wildSignFast equation data = 1 := by decide +kernel
end C36_a1
theorem refuse_other_primes : tateWitness? C27_a1.equation 0 = none ∧
    tateWitness? C27_a1.equation 1 = none ∧ tateWitness? C27_a1.equation 5 = none := by decide +kernel
theorem refuse_singular : wildData? ⟨0,0,0,0,0⟩ = none := by decide +kernel
end VerifiedLcalc.EllipticCurve.WildExamples
