module

public import VerifiedLcalc.LmfdbSupplement
public import Mathlib.Data.String.Basic
public import Mathlib.Data.List.Sort

@[expose] public section
namespace VerifiedLcalc.Lmfdb

def labelKey (s : String) : Nat :=
  let cs := s.toList.map Char.toNat
  (cs ++ List.replicate (16 - cs.length) 0).foldl (fun n c => 257 * n + c) 0

def sortedAllLabels : List Nat := allCases.map (fun c => labelKey c.input.label)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Adjacent comparisons give a small kernel certificate of global uniqueness. -/
theorem labels_strictly_sorted : sortedAllLabels.IsChain (· < ·) := by
  unfold sortedAllLabels
  decide +kernel

theorem all_labels_nodup : (allCases.map (·.input.label)).Nodup := by
  have hs : sortedAllLabels.Nodup :=
    (List.isChain_iff_pairwise.mp labels_strictly_sorted).imp (fun h => ne_of_lt h)
  have hn : ((allCases.map (·.input.label)).map labelKey).Nodup := by
    simpa only [sortedAllLabels, List.map_map, Function.comp_def] using hs
  exact List.Nodup.of_map labelKey hn

end VerifiedLcalc.Lmfdb
