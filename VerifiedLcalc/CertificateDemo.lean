module

public import VerifiedLcalc.Certificate
public import VerifiedLcalc.Demo

@[expose] public section

namespace VerifiedLcalc.Examples

/-- This demo identity is not a content digest. Lake tracks the actual imported
sources; persistent content-addressed caching is a later implementation step. -/
def cubicRequest : Artifacts.Request :=
  { formatVersion := 1
    subject := .monomial 3
    settings := ⟨0, 0, 3⟩
    build := ⟨"leanprover/lean4:v4.36.0-rc2",
      "3440367ed1804626334f13a3a534a9cbb3385a59",
      "exact-polynomial-demo-v1", "derivative-box-checker-v1"⟩ }

/-- Producer output contains finite evidence rather than a call to the producer. -/
def cubicArtifact : Artifacts.Artifact := ⟨cubicRequest, 3, cubicBoxes⟩

theorem cubicArtifact_checks : Artifacts.check cubicRequest cubicArtifact = true := by decide

/-- A different normalization, input, version, or resource plan invalidates reuse. -/
example : Artifacts.check { cubicRequest with subject := .monomial 4 } cubicArtifact = false := by
  decide
example : Artifacts.check { cubicRequest with formatVersion := 2 } cubicArtifact = false := by
  decide
example : Artifacts.check
    { cubicRequest with settings := ⟨0, 0, 4⟩ } cubicArtifact = false := by decide
example : Artifacts.check
    { cubicRequest with build := { cubicRequest.build with checkerRevision := "v2" } }
    cubicArtifact = false := by decide
-- Unsupported formats are rejected even if the embedded and expected requests agree.
example : Artifacts.check { cubicRequest with formatVersion := 2 }
    { cubicArtifact with request := { cubicRequest with formatVersion := 2 } } = false := by decide
-- Wrong claimed rank, insufficient boxes, and uncertain zeros cannot pass.
example : Artifacts.check cubicRequest { cubicArtifact with rank := 2 } = false := by decide
-- A matching request still fails when the witness exceeds its derivative budget.
example : Artifacts.check
    { cubicRequest with settings := ⟨0, 0, 2⟩ }
    { cubicArtifact with request := { cubicRequest with settings := ⟨0, 0, 2⟩ } } = false := by
  decide
example : Artifacts.check cubicRequest
    { cubicArtifact with derivativeBoxes := cubicBoxes.take 3 } = false := by decide
example : Artifacts.check cubicRequest
    { cubicArtifact with derivativeBoxes := [⟨-1, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩,
      ⟨0, 0, 0, 0⟩, ⟨6, 6, 0, 0⟩] } = false := by decide

/-- First real-curve request: exact 11.a2 equation, arithmetic center s=1.
This request has no analytic certificate yet. -/
def firstCurveRequest : Artifacts.Request :=
  { cubicRequest with subject := .ellipticCurve ⟨0, -1, 1, -10, -20⟩ .arithmetic }

example : Artifacts.check firstCurveRequest cubicArtifact = false := by decide
-- Relabeling finite data can pass its data checks, but supplies no analytic proof.
example : Artifacts.check firstCurveRequest
    { cubicArtifact with request := firstCurveRequest } = true := by decide
-- An arithmetic certificate cannot be reused at the unitary center.
example : Artifacts.check
    { firstCurveRequest with subject := .ellipticCurve ⟨0, -1, 1, -10, -20⟩ .unitary }
    { cubicArtifact with request := firstCurveRequest } = false := by decide
-- Neither can a certificate for a different exact Weierstrass equation.
example : Artifacts.check
    { firstCurveRequest with subject := .ellipticCurve ⟨0, -1, 1, -11, -20⟩ .arithmetic }
    { cubicArtifact with request := firstCurveRequest } = false := by decide

end VerifiedLcalc.Examples
