import VerifiedLcalcTests.Fixtures.SerreInvariants
import Lean

open Lean Elab Command
open VerifiedLcalc VerifiedLcalcTests.SerreInvariants

example : (Serre37.certificate.serreInvariants.get (by rfl)).rows = [(37, 38, 1)] := rfl

example : (Serre69.certificate.serreInvariants.get (by rfl)).rows =
    [(2, 2, 3), (3, 4, 23), (23, 24, 3)] := rfl

example : (Serre11.certificate.serreInvariants.get (by rfl)).rows =
    [(5, 2, 1), (11, 12, 1)] := rfl

theorem serre69_dyadic_complete (w n : ℕ) :
    (2, w, n) ∈ (Serre69.certificate.serreInvariants.get (by rfl)).rows ↔
      (w, n) = (2, 3) := by
  change (2, w, n) ∈ [(2, 2, 3), (3, 4, 23), (23, 24, 3)] ↔ _
  simp

run_cmd do
  for name in [``Serre37.certificate, ``Serre37.serre_invariants, ``Serre69.certificate,
      ``Serre69.serre_invariants, ``serre69_dyadic_complete] do
    for axiomName in ← liftTermElabM (Lean.collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"
