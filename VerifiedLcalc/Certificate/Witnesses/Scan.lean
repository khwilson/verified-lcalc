/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Certificate.Artifacts.ScanWitness

/-! Typed finite rank certificate records. -/

@[expose] public section

namespace VerifiedLcalc

/-- A proof-carrying finite rank contract. Its proof is entirely about the
supplied rectangles; the executable scan equation is exposed by compatibility. -/
structure Certificate (bs : List Box) where
  /-- First derivative index whose box excludes zero. -/
  rank : Nat
  /-- Finite mathematical witness for this rank and these boxes. -/
  sound : Witness bs rank

end VerifiedLcalc
