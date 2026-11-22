import VerifiedLcalcTests.Fixtures.TwoFactorTorsion

/-! The compiled fixture exports the full structure and both generator images. -/

example : Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) = 8 :=
  C120b4.torsion

example : ∃ e : ZMod 2 × ZMod 4 ≃+ AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point,
    (e (1, 0) : (C120b4.curve.baseChange ℚ).toAffine.Point) =
      C120b4.torsion_generators.point ⟨0, by decide⟩ ∧
    (e (0, 1) : (C120b4.curve.baseChange ℚ).toAffine.Point) =
      C120b4.torsion_generators.point ⟨1, by decide⟩ :=
  C120b4.torsion_structure.2

-- Prime support follows from the actual subgroup cardinality.
example (p : ℕ) :
    p ∈ ([2] : List ℕ) ↔ p.Prime ∧
      p ∣ Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) := by
  rw [C120b4.torsion]
  change _ ↔ p.Prime ∧ p ∣ 8
  rw [← Nat.mem_primeFactorsList (by decide : (8 : ℕ) ≠ 0)]
  rw [show Nat.primeFactorsList 8 = [2, 2, 2] by decide +kernel]
  simp
