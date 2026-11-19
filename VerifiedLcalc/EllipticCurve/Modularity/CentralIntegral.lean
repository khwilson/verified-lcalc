module

public import VerifiedLcalc.EllipticCurve.Modularity.Realization
public import VerifiedLcalc.Numerics.MellinSplit

@[expose] public section

namespace VerifiedLcalc.Modularity
open Set MeasureTheory

noncomputable def ModularRealization.imaginaryFunction {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (t : ℝ) : ℂ :=
  m.form (UpperHalfPlane.ofComplex (Complex.I * (t / Real.sqrt m.level)))

theorem ModularRealization.central_mellin {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) :
    m.formL 1 = (2 * Real.pi / Real.sqrt m.level : ℂ) *
      mellin m.imaginaryFunction 1 := by
  let _ := m.arithmetic
  have hpos : 0 < Real.sqrt (m.level : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)
  have hscale := mellin_comp_mul_right
    (fun t : ℝ => m.form (UpperHalfPlane.ofComplex (Complex.I * t))) 1
    (a := (Real.sqrt m.level)⁻¹) (inv_pos.mpr hpos)
  have hΛ := congrFun (CuspForm.Λ_eq_mellin (by decide : (0 : ℤ) < 2) m.form) 1
  have hL := ModularForm.L_apply_of_ne_zero (by decide : (0 : ℤ) < 2) m.form
    (by norm_num : (1 : ℂ) ≠ 0)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsqrt : (Real.sqrt m.level : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [Complex.cpow_neg, Complex.cpow_one, Complex.ofReal_inv, inv_inv,
    smul_eq_mul] at hscale
  have hscale' : mellin m.imaginaryFunction 1 =
      (Real.sqrt m.level : ℂ) *
        mellin (fun t : ℝ => m.form (UpperHalfPlane.ofComplex (Complex.I * t))) 1 := by
    convert hscale using 2
    funext t
    simp [ModularRealization.imaginaryFunction, Complex.ofReal_mul,
      Complex.ofReal_inv, div_eq_mul_inv]
  rw [hΛ] at hL
  change ModularForm.L (by decide : (0 : ℤ) < 2) m.form 1 = _
  rw [hL, Complex.Gammaℂ_one, hscale']
  field_simp

theorem ModularRealization.central_mellin_convergent {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) : MellinConvergent m.imaginaryFunction 1 := by
  let _ := m.arithmetic
  have hpos : 0 < (Real.sqrt m.level)⁻¹ := by
    apply inv_pos.mpr
    exact Real.sqrt_pos.mpr (by exact_mod_cast m.positiveLevel)
  have hf := (CuspForm.isStrongFEPair (by decide : (0 : ℤ) < 2) m.form).hasMellin 1 |>.1
  have h := (MellinConvergent.comp_mul_left hpos).mpr hf
  convert h using 1
  funext t
  simp [ModularRealization.imaginaryFunction, ModularForm.weakFEPair, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_comm]

theorem ModularRealization.central_upper_mellin {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) :
    m.formL 1 = (2 * Real.pi / Real.sqrt m.level : ℂ) * (1 + (m.rootNumber : ℂ)) *
      mellin ((Ioi (1 : ℝ)).indicator m.imaginaryFunction) 1 := by
  rw [m.central_mellin,
    Numerics.mellin_one_split m.imaginaryFunction m.rootNumber m.central_mellin_convergent
      (by
        intro t ht
        simpa [ModularRealization.imaginaryFunction, Complex.ofReal_div, Complex.ofReal_inv] using m.frickeImaginaryAxis t ht)]
  ring

/-- Odd Fricke sign forces exact central vanishing. This conclusion follows
from the proved integral identity, not from a numerical zero cutoff. -/
theorem ModularRealization.central_zero_of_negative_sign {e : (WeierstrassCurve ℤ)}
    (m : ModularRealization e) (hw : m.rootNumber = -1) : m.formL 1 = 0 := by
  rw [m.central_upper_mellin, hw]
  simp

end VerifiedLcalc.Modularity
