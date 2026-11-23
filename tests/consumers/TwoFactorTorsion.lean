import VerifiedLcalcTests.Fixtures.TwoFactorTorsion

/-! The compiled fixture exports the full structure and both generator images. -/

open VerifiedLcalc Lean Elab Command

noncomputable section

example : Nat.card (AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point) = 8 :=
  C120b4.torsion

example : ∃ e : ZMod 2 × ZMod 4 ≃+ AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point,
    (e (1, 0) : (C120b4.curve.baseChange ℚ).toAffine.Point) =
      C120b4.torsion_generators.point ⟨0, by decide⟩ ∧
    (e (0, 1) : (C120b4.curve.baseChange ℚ).toAffine.Point) =
      C120b4.torsion_generators.point ⟨1, by decide⟩ :=
  C120b4.torsion_structure.2

private def torsion := C120b4.certificate.torsion
private def presentation := torsion.presentation.get (by decide +kernel)
private def generators := torsion.generators.getD ⟨0, Fin.elim0⟩

example : List.ofFn presentation.factor = [2, 4] := rfl
example : List.ofFn (fun i => (presentation.indices i).val) = [0, 1] := rfl
example : torsion.orders.map
    (fun orders => List.ofFn (fun i => ((orders i).val : ℕ))) = some [2, 4] := rfl

/-- The two factor generators map to the submitted torsion points in their certified order. -/
theorem imported_generator_images :
    ∃ e : (∀ j, ZMod (presentation.factor j)) ≃+
        AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point,
      (e (Pi.single (0 : Fin 2) 1) : (C120b4.curve.baseChange ℚ).toAffine.Point) =
        generators.2 ⟨0, by decide +kernel⟩ ∧
      (e (Pi.single (1 : Fin 2) 1) : (C120b4.curve.baseChange ℚ).toAffine.Point) =
        generators.2 ⟨1, by decide +kernel⟩ := by
  obtain ⟨e, maps⟩ := presentation.realization
  exact ⟨e, maps (0 : Fin 2), maps (1 : Fin 2)⟩

example : AddSubgroup.closure (Set.range generators.2) =
    AddCommGroup.torsion (C120b4.curve.baseChange ℚ).toAffine.Point :=
  (torsion.generation.get (by decide +kernel)).down

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
      `C120b4.certificate, `C120b4.torsion_generators.generates_torsion,
      ``imported_prime_support, ``imported_generator_images] do
    for ax in ← liftTermElabM <| Lean.collectAxioms name do
      unless standard.contains ax do
        throwError "Unexpected torsion-structure axiom {ax} in {name}"
