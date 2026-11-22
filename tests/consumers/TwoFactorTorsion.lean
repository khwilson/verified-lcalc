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

private def checkedStructure : TwoFactorTorsionFacts C120b4.curve :=
  C120b4.certificate.torsion.twoFactorStructure.get (by decide +kernel)

example : checkedStructure.invariantFactors = [2, 4] := rfl

example : Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) =
    checkedStructure.order := checkedStructure.cardinality

example : (checkedStructure.equivalence (1, 0) :
    (C120b4.curve.baseChange ℚ).toAffine.Point) = checkedStructure.firstGenerator :=
  checkedStructure.maps_first

example : (checkedStructure.equivalence (0, 1) :
    (C120b4.curve.baseChange ℚ).toAffine.Point) = checkedStructure.secondGenerator :=
  checkedStructure.maps_second

-- Prime support follows from the actual subgroup cardinality.
example (p : ℕ) :
    p ∈ ([2] : List ℕ) ↔ p.Prime ∧
      p ∣ Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) := by
  rw [C120b4.torsion]
  change _ ↔ p.Prime ∧ p ∣ 8
  rw [← Nat.mem_primeFactorsList (by decide : (8 : ℕ) ≠ 0)]
  rw [show Nat.primeFactorsList 8 = [2, 2, 2] by decide +kernel]
  simp

private def checkedPrimeSupport : TorsionPrimeSupportFacts C120b4.curve :=
  C120b4.certificate.torsion.primeSupport.get (by decide +kernel)

example : checkedPrimeSupport.primes = [2] := rfl

example (p : ℕ) : p ∈ checkedPrimeSupport.primes ↔ p.Prime ∧
    p ∣ Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) :=
  checkedPrimeSupport.exact_support p

theorem imported_prime_support (p : ℕ) : p ∈ checkedPrimeSupport.primes ↔ p.Prime ∧
    p ∣ Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) :=
  checkedPrimeSupport.exact_support p

run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [`C120b4.torsion_structure_equiv,
      `C120b4.torsion_structure_first_image, `C120b4.torsion_structure_second_image,
      `C120b4.torsion_structure_cardinality, `C120b4.torsion_primes_exact,
      `C120b4.certificate, ``imported_prime_support] do
    for ax in ← liftTermElabM <| Lean.collectAxioms name do
      unless standard.contains ax do
        throwError "Unexpected torsion-structure axiom {ax} in {name}"
