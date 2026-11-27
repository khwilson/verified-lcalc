/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Tactic.CertifyEC
import VerifiedLcalc.EllipticCurve.SparsePointCount

/-! # The published 37.a1 trace-hash report and its full coefficient vector

Each finite point order isolates one Hasse count. The verified full vector is
supplied to the arithmetic checker for the native class report at
https://www.lmfdb.org/EllipticCurve/Q/data/37.a1?_format=json.
The proof identifies the coefficients of the displayed 37.a1 equation.
-/

@[expose] public section

namespace VerifiedLcalcTests.TraceHash37

open VerifiedLcalc EllipticCurve

/-- Integral equation of LMFDB 37.a1. -/
abbrev curve : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-- Coefficient fixture for the entire published prime interval. -/
def coefficients : List ℤ :=
  [-58, 51, -42, -92, -3, 42, -14, 44, 70, 41, 34, 117, 38, 84, 14, -64,
  30, 35, -66, -4, -50, 4, 10, 77, -55, 2, 88, -62, -87, -32, 37, -69,
  -17, -33, 88, -78, 48, -84, -122, -35, 25, 56, -24, -50, 64, -87, -105, 43,
  -25, 4, 47, 47, 96, -57, 108, 12, -63, -34, 122, 97, 11, 84, -44, -56,
  52, 50, -29, 87, 38, 60, 120, 60, -42, -53, 45, 114, 88, -39, -78, -81,
  -108, -48, -85, -23, 55, 53, -86, 30, 31, -116, -60, 46, -22, 51, 57, 37,
  -50, 49, -62, -60, -103, 54, 82, 22, -64, 46, -66, 121, -51, -15, -56, 40,
  27, -40, 86, 36, 84, -106, 85, -67, -76, 60, 101, -72, 69, 29, 18, -112,
  30, -68, 136, 49, -66, -91, 18, 52, 70, -86, -80, -64, 88, 126, 22, 16,
  -113, 80, 53, -59, 74, -113, -112, -66, -132, -106, 34, -68, 15, 120, 18, 135,
  -47, 18, 48, -102, -130, -20, 122, 38, -22, 46, 96, 86, 132, -93, 75, -136,
  -42, -4, -11, -40, -90, -106, 58, 64, 25, -6, -102, 100, 98, -92, -30, -30,
  80, -101, -99, -124, 92, -28, -117, -25, 28, 96, -135, 61, 62, 93, -78, 21,
  -126, 121, 148, -30, 112, 49, -72, 108, -109, 58, 43, -154, -138, 54, 74, -93,
  -48, 12, -92, -64, 67, 73, -106, -106, 16, 2, -44, 71, 45, 120, 100, -44,
  -98, -66, -86, -10, 14, 120, 20, 12, 35, 53, -15, -52, -10, -4, -57, 98,
  -71, 2, 81, -108, -82, -21, 93, -56, 97, 47, -5, -50, 42, 65, 50, 113,
  15, -26, 26, 14, -32, 83, 87, -58, 84, -52, 2, 108, 74, -118, 102, 90,
  -28, -72, -65, 80, -57, 60, -93, -36, -8, -50, 56, -157, -74, 83, 14, 127,
  87, -57, -122, 24, -94, -80, -114, -78, -154, -30, -153, 37, -83, 63, 144, 8,
  -56, 52, 100, 85, -64, 82, -48, 14, -55, -144, -143, -98, 134, 117, 164, -89,
  60, -60, -116, 100, -73, -80, -13, -154, 87, -91, -24, -66, 166, -59, -108, 20,
  -99, -32, -126, 146, -73, -120, 37, -64, 68, -100, -118, 31, -122, -86, -160, 166,
  24, 58, 118, -2, -27, 12, -61, 20, 112, 130, -4, -108, 112, 149, 26, -24,
  108, -68, 47, 44, 15, 14, -125, 94, 103, 157, -155, -32, -31, 12, 66, 75,
  -136, 50, -74, 47, -20, -141, 150, -93, 114, -72, -91, 40, -37, -5, -63, 25,
  -62, 40, 52, 108, 131, -20, 6, 83, 161, -6, -6, -142, -2, -32, 74, 114,
  -114, -96, -3, 15, 7, -94, 62, -8, 0, -82, -69, 122, -94, -133, -49, 16,
  4, 174, 126, 24, 118, -23, 128, -24, -108, -58, 44, -163, 33, 66, -100, -102]

private def exceptions : List (ℕ × (ℕ × ℕ)) :=
  [(4483, (4, 3679)), (4591, (3, 3413)), (4943, (3, 2673)), (5099, (16, 2565)),
   (5153, (3, 3724)), (5381, (4, 2754)), (5477, (8, 4517)), (5521, (3, 4327)),
   (5569, (5, 3996)), (6067, (3, 5736)), (6211, (7, 3195)), (6229, (5, 6005)),
   (6329, (3, 4294)), (6553, (3, 3875)), (6659, (5, 5772)), (7757, (3, 7325))]

private def witnessPoint (p : ℕ) : ℕ × ℕ :=
  ((exceptions.find? fun row => row.1 == p).map Prod.snd).getD (0, 0)

private abbrev TracePrime := {p // p ∈ lmfdbTraceHashPrimes}

private theorem tracePrime_isPrime (p : TracePrime) : p.val.Prime := by
  rcases p with ⟨p, hp⟩
  change p.Prime
  rw [lmfdbTraceHashPrimes_eq] at hp
  exact of_decide_eq_true (List.mem_filter.mp hp).2

private def rows : List (TracePrime × ℤ) :=
  lmfdbTraceHashPrimes.attach.zip coefficients

private def checkRow (row : TracePrime × ℤ) : Bool :=
  letI : Fact row.1.val.Prime := ⟨tracePrime_isPrime row.1⟩
  let point := witnessPoint row.1.val
  pointOrderTraceCheck curve row.1.val point.1 point.2 row.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
-- The kernel verifies 464 exact point orders and Hasse isolations in one list traversal.
private theorem allRowsChecked : rows.all checkRow = true := by decide +kernel

instance : (curve.baseChange ℚ).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

/-- The full reported vector is the arithmetic coefficient vector of 37.a1. -/
theorem coefficients_correct :
    coefficients = lmfdbTraceHashPrimes.map (fun p => (curve.baseChange ℚ).LFunction p) := by
  have hlength : lmfdbTraceHashPrimes.attach.length = coefficients.length :=
    List.length_attach.trans (lmfdbTraceHashWeights_length.symm.trans (by decide +kernel))
  have hfirst : rows.map Prod.fst = lmfdbTraceHashPrimes.attach := List.map_fst_zip hlength.le
  have hprimes : rows.map (fun row => row.1.val) = lmfdbTraceHashPrimes := by
    rw [show (fun row : TracePrime × ℤ => row.1.val) = Subtype.val ∘ Prod.fst from rfl,
      ← List.map_map, hfirst, List.attach_map_subtype_val]
  have hsecond : rows.map Prod.snd = coefficients := List.map_snd_zip hlength.ge
  rw [← hprimes, ← hsecond, List.map_map]
  apply List.map_congr_left
  intro row hrow
  let : Fact row.1.val.Prime := ⟨tracePrime_isPrime row.1⟩
  let point := witnessPoint row.1.val
  exact (pointOrderTraceCheck_sound curve row.1.val point.1 point.2 row.2 (by decide +kernel)
    (List.all_eq_true.mp allRowsChecked row hrow)).symm

/-- Supply the checked complete native coefficient vector. -/
def proofs : IntegralCurveProofs curve :=
  { traceHashCoefficients := some ⟨coefficients, coefficients_correct⟩ }

certify_ec Checked from_json "../../fixtures/lmfdb/37.a1-trace-hash-source.json"
  with_proofs proofs

end VerifiedLcalcTests.TraceHash37
