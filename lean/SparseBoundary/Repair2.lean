import SparseBoundary.MinorGroups

import SparseBoundary.GraphSubdivision
import SparseBoundary.GraphPerm

namespace SparseBoundary.Repair2

open Graph MinorSearch

private def realization : Graph 7 := ⟨241503⟩
private def initial : Nat := 0xfeeaeeeefefaeeffffeaefeffffbeffe
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

private theorem core_planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

private def stage1 : Graph 8 := ⟨30109172⟩

private theorem stage1_planar : stage1.Planar :=
  degree_two_extension (G:=stage1) core_planar 3 4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def stage0 : Graph 9 := ⟨7610284896⟩

private theorem stage0_planar : stage0.Planar :=
  degree_two_extension (G:=stage0) stage1_planar 3 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem planaric_repair : Planaric [6, 5, 5, 5, 5, 3, 3, 2, 2] := by
  apply (planaric_perm (d:=[2, 2, 6, 5, 5, 5, 5, 3, 3]) (by decide +kernel)).mp
  refine ⟨stage0, ?_, stage0_planar⟩
  show ∀ i : Fin 9, stage0.degree i = ([2, 2, 6, 5, 5, 5, 5, 3, 3] : List Nat)[i]
  decide +kernel

end SparseBoundary.Repair2
