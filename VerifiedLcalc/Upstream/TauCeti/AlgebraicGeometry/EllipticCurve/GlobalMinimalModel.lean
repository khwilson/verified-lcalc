/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import VerifiedLcalc.Upstream.TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-! Selected upstream excerpt: the canonical global-minimality predicate and
its introduction/elimination interface. Integrality descent, semi-global
minimality and variable-change theorems are not included in this excerpt.
The upstream definition is adapted from LeanBridge
(`github.com/CBirkbeck/LeanBridge`, Apache-2.0), `LeanBridge/ForMathlib/4-EC.lean`
at `JaneShi99/LeanBridge@d84dd305` (branch `formalize/ec-defs`), by Jane Shi.
See PROVENANCE.json. -/

public section

namespace WeierstrassCurve

open IsDedekindDomain

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **A globally minimal Weierstrass equation** (LMFDB `ec.global_minimal_model`): `W` is minimal
over the discrete valuation ring `Localization.AtPrime v.asIdeal` at every height-one prime `v` of
`O`. Integrality over `O` is not assumed; it is the theorem `IsGlobalMinimal.isIntegral`. The
ellipticity instance keeps the predicate to elliptic curves, the setting in which the invariants
derived from it make sense; the definition itself does not consume it, which its binder name
records. -/
def IsGlobalMinimal (W : WeierstrassCurve K) [_hE : W.IsElliptic] : Prop :=
  ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W

variable {O} in
/-- Global minimality is minimality at every height-one prime. This is the interface to
`WeierstrassCurve.IsGlobalMinimal` outside its defining module. -/
@[simp]
theorem isGlobalMinimal_iff {W : WeierstrassCurve K} [W.IsElliptic] :
    IsGlobalMinimal O W ↔
      ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W :=
  Iff.rfl

variable {O} in
/-- A globally minimal equation is minimal at each height-one prime. -/
theorem IsGlobalMinimal.isMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) (v : HeightOneSpectrum O) :
    IsMinimal (Localization.AtPrime v.asIdeal) W :=
  h v

variable {O} in
/-- An equation minimal at every height-one prime is globally minimal. -/
theorem IsGlobalMinimal.of_forall_isMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    (h : ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W) :
    IsGlobalMinimal O W :=
  h


end WeierstrassCurve

end
