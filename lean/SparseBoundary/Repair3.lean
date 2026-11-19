import SparseBoundary.MinorGroups

namespace SparseBoundary.Repair3

open Graph MinorSearch

private def realization : Graph 7 := ⟨382879⟩
private def initial : Nat := 0xffeeeaeaffecefefffffeafbfffdeffe
private def catalog : Array (Option Nat) := ((List.range 128).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 7).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 7 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

def sevenGraph : Graph 7 := realization

theorem sevenGraph_planar : sevenGraph.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

theorem planaric_repair : Planaric [5, 5, 4, 4, 4, 3, 3] := by
  refine ⟨realization, ?_, sevenGraph_planar⟩
  show ∀ i : Fin 7, realization.degree i = ([5, 5, 4, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

end SparseBoundary.Repair3
