import SparseBoundary.MinorGroups

namespace SparseBoundary.Repair5

open Graph MinorSearch

private def realization : Graph 8 := ⟨144887039⟩
private def initial : Nat := 0xeaeaeaeaeaeafafbeaeaeaeaeaeafafbeaeaeaeaeaeafafbeeefeeefeeeffffe
private def catalog : Array (Option Nat) := ((List.range 256).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 8).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 8 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

theorem planaric_repair : Planaric [7, 5, 5, 3, 3, 3, 3, 3] := by
  refine ⟨realization, ?_, planar_of_groups realization catalog initial table
    cover_ok table_ok (by decide +kernel) (by decide +kernel)⟩
  show ∀ i : Fin 8, realization.degree i = ([7, 5, 5, 3, 3, 3, 3, 3] : List Nat)[i]
  decide +kernel

end SparseBoundary.Repair5
