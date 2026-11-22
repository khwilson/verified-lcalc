/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import VerifiedLcalc.Upstream.TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
public import VerifiedLcalc.Upstream.TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-! Selected semistability interface from TauCeti. -/

public section

namespace WeierstrassCurve

open IsDedekindDomain

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {F : Type*} [Field F] [Algebra O F] [IsFractionRing O F]

/-- **Semistability over a Dedekind domain**: at every height-one prime, a local minimal equation
has no additive reduction. Equivalently, the reduction is good or multiplicative everywhere.

The ellipticity instance excludes singular cubics. -/
def IsSemistable (W : WeierstrassCurve F) [_hE : W.IsElliptic] : Prop :=
  ∀ v : HeightOneSpectrum O,
    ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
      (Localization.AtPrime v.asIdeal)

variable {O}

/-- Semistability means that every local minimal equation has no additive reduction. -/
theorem isSemistable_iff {W : WeierstrassCurve F} [W.IsElliptic] :
    IsSemistable O W ↔ ∀ v : HeightOneSpectrum O,
      ¬ (W.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction
        (Localization.AtPrime v.asIdeal) :=
  Iff.rfl

end WeierstrassCurve

end
