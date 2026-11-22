/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Witnesses.DegreeTwoIsogeny

/-! # Compatibility path and derived theorem for degree-two isogenies -/

@[expose] public section

namespace VerifiedLcalc
open TauCeti

/-- The certified edge attains the minimum degree among all rational isogenies. -/
theorem DegreeTwoIsogenyFact.isLeast_degree {source target : WeierstrassCurve ℤ}
    (fact : DegreeTwoIsogenyFact source target) :
    IsLeast (Set.range fun φ :
      Isogeny (source.baseChange ℚ).toAffine (target.baseChange ℚ).toAffine => φ.degree) 2 := by
  refine ⟨⟨fact.isogeny, fact.degree_eq⟩, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact fact.degree_le φ

end VerifiedLcalc
