import SparseBoundary.MinorGroups

namespace SparseBoundary.Graph.ContractionLayer6
open MinorSearch

def graphs : Array (Graph 6) := #[⟨0x75ef⟩, ⟨0x6faf⟩]

set_option maxRecDepth 16384
set_option maxHeartbeats 0

private def g0 : Graph 6 := ⟨0x75ef⟩
private def mask0 : Nat := 0xfffffbfbfafffbfe
private def cat0 : Array (Option Nat) := ((List.range 64).map fun m =>
  if mask0.testBit m then some (
    ((List.finRange 6).filter (fun v => m.testBit v.val)).foldl (fun s v => s ||| neigh g0 v) 0)
  else none).toArray
private def tab0 := makeTable 6 cat0 mask0
private theorem known0 : g0.Planar := planar_of_groups g0 cat0 mask0 tab0
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def g1 : Graph 6 := ⟨0x6faf⟩
private def mask1 : Nat := 0xffffffeffffdfbfe
private def cat1 : Array (Option Nat) := ((List.range 64).map fun m =>
  if mask1.testBit m then some (
    ((List.finRange 6).filter (fun v => m.testBit v.val)).foldl (fun s v => s ||| neigh g1 v) 0)
  else none).toArray
private def tab1 := makeTable 6 cat1 mask1
private theorem known1 : g1.Planar := planar_of_groups g1 cat1 mask1 tab1
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem known : ∀ G∈graphs,G.Planar := by
  intro G h
  change G∈([g0,g1] : List (Graph 6)).toArray at h
  simp only [List.mem_toArray,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl
  · exact known0
  · exact known1

end SparseBoundary.Graph.ContractionLayer6
