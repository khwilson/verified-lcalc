import VerifiedLcalcTests.Fixtures.TwoFactorTorsion

open VerifiedLcalc Lean Elab Command

noncomputable section

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
example : 0 < checkedStructure.secondOrder := checkedStructure.secondOrder_pos
example : 2 ∣ checkedStructure.secondOrder := checkedStructure.first_factor_dvd_second

example : Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) =
    checkedStructure.order := checkedStructure.cardinality

example : (checkedStructure.equivalence (1, 0) :
    (C120b4.curve.baseChange ℚ).toAffine.Point) = checkedStructure.firstGenerator :=
  checkedStructure.maps_first

example : (checkedStructure.equivalence (0, 1) :
    (C120b4.curve.baseChange ℚ).toAffine.Point) = checkedStructure.secondGenerator :=
  checkedStructure.maps_second

private def checkedPrimeSupport : TorsionPrimeSupportFacts C120b4.curve :=
  C120b4.certificate.torsion.primeSupport.get (by decide +kernel)

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
