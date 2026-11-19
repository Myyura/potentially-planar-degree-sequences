import SparseBoundary.MinorGroups
import SparseBoundary.GraphSubdivision
import SparseBoundary.GraphPerm

/-! Explicit finite witnesses for the predecessor repairs in the two
    leaf-restoration arguments. The small residuals are tested directly
    for both forbidden minors; suppressed degree-two vertices and leaves
    are restored by general graph theorems. -/

namespace SparseBoundary.LeafRepair1

open Graph MinorSearch

private def realization : Graph 6 := ⟨11775⟩
private def initial : Nat := 0xfeeeffeffefffffe
private def catalog : Array (Option Nat) := ((List.range 64).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 6).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 6 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

private theorem core_planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

theorem planaric_repair : Planaric [5, 5, 4, 4, 3, 3] := by
  apply (planaric_perm (d:=[5, 5, 4, 4, 3, 3]) (by decide +kernel)).mp
  refine ⟨realization, ?_, core_planar⟩
  show ∀ i : Fin 6, realization.degree i = ([5, 5, 4, 4, 3, 3] : List Nat)[i]
  decide +kernel

theorem predecessor_planaric : Planaric [5, 5, 4, 4, 4, 3, 1] := by
  have h := planaric_attach_leaf planaric_repair 4
  exact (planaric_perm (e:=[5, 5, 4, 4, 4, 3, 1]) (by decide +kernel)).mp h

end SparseBoundary.LeafRepair1

namespace SparseBoundary.LeafRepair2

open Graph MinorSearch

private def realization : Graph 6 := ⟨11775⟩
private def initial : Nat := 0xfeeeffeffefffffe
private def catalog : Array (Option Nat) := ((List.range 64).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 6).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 6 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

private theorem core_planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

private def stage1 : Graph 7 := ⟨737212⟩

private theorem stage1_planar : stage1.Planar :=
  degree_two_extension (G:=stage1) core_planar 2 4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def stage0 : Graph 8 := ⟨93288354⟩

private theorem stage0_planar : stage0.Planar :=
  degree_two_extension (G:=stage0) stage1_planar 1 4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem planaric_repair : Planaric [6, 5, 5, 5, 4, 3, 2, 2] := by
  apply (planaric_perm (d:=[2, 2, 6, 5, 5, 5, 4, 3]) (by decide +kernel)).mp
  refine ⟨stage0, ?_, stage0_planar⟩
  show ∀ i : Fin 8, stage0.degree i = ([2, 2, 6, 5, 5, 5, 4, 3] : List Nat)[i]
  decide +kernel

theorem predecessor_planaric : Planaric [6, 5, 5, 5, 5, 3, 2, 2, 1] := by
  have h := planaric_attach_leaf planaric_repair 4
  exact (planaric_perm (e:=[6, 5, 5, 5, 5, 3, 2, 2, 1]) (by decide +kernel)).mp h

end SparseBoundary.LeafRepair2

namespace SparseBoundary.LeafRepair3

open Graph MinorSearch

private def realization : Graph 7 := ⟨260843⟩
private def initial : Nat := 0xfefefefcfeeefafffffffffdffafbbbe
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

theorem planaric_repair : Planaric [5, 4, 4, 4, 4, 4, 3] := by
  apply (planaric_perm (d:=[5, 4, 4, 4, 4, 4, 3]) (by decide +kernel)).mp
  refine ⟨realization, ?_, core_planar⟩
  show ∀ i : Fin 7, realization.degree i = ([5, 4, 4, 4, 4, 4, 3] : List Nat)[i]
  decide +kernel

theorem predecessor_planaric : Planaric [5, 4, 4, 4, 4, 4, 4, 1] := by
  have h := planaric_attach_leaf planaric_repair 6
  exact (planaric_perm (e:=[5, 4, 4, 4, 4, 4, 4, 1]) (by decide +kernel)).mp h

/-- A seven-core support with degree profile (5,4,4,4,4,4,3). -/
def oneThreeBase : Graph 7 := realization

theorem oneThreeBase_planar : oneThreeBase.Planar := core_planar

end SparseBoundary.LeafRepair3

namespace SparseBoundary.LeafRepair4

open Graph MinorSearch

private def realization : Graph 7 := ⟨1150463⟩
private def initial : Nat := 0xeeeeeeefeeeeeeefeeeeeeeffefffffe
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

theorem planaric_repair : Planaric [6, 6, 4, 3, 3, 3, 3] := by
  apply (planaric_perm (d:=[6, 6, 4, 3, 3, 3, 3]) (by decide +kernel)).mp
  refine ⟨realization, ?_, core_planar⟩
  show ∀ i : Fin 7, realization.degree i = ([6, 6, 4, 3, 3, 3, 3] : List Nat)[i]
  decide +kernel

theorem predecessor_planaric : Planaric [6, 6, 5, 3, 3, 3, 3, 1] := by
  have h := planaric_attach_leaf planaric_repair 2
  exact (planaric_perm (e:=[6, 6, 5, 3, 3, 3, 3, 1]) (by decide +kernel)).mp h

/-- The double fan over a length-two path and a disjoint edge. -/
def doubleFan : Graph 7 := realization

theorem doubleFan_planar : doubleFan.Planar := core_planar

/-- The first two poles together with the degree-four vertex form the
    triangle along which the seven-core multiplicities are increased. -/
theorem triangle_support : ∃ H : Graph 7, H.Planar ∧
    List.ofFn H.degree = [6,6,4,3,3,3,3] ∧
    H.adj 0 1 = true ∧ H.adj 0 2 = true ∧ H.adj 1 2 = true :=
  ⟨realization, core_planar, by decide +kernel, by decide, by decide, by decide⟩

end SparseBoundary.LeafRepair4

namespace SparseBoundary.LeafRepair5

open Graph MinorSearch

private def realization : Graph 7 := ⟨1150463⟩
private def initial : Nat := 0xeeeeeeefeeeeeeefeeeeeeeffefffffe
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

private def stage0 : Graph 8 := ⟨147012541⟩

private theorem stage0_planar : stage0.Planar :=
  degree_two_extension (G:=stage0) core_planar 0 2 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem planaric_repair : Planaric [7, 6, 5, 3, 3, 3, 3, 2] := by
  apply (planaric_perm (d:=[2, 7, 6, 5, 3, 3, 3, 3]) (by decide +kernel)).mp
  refine ⟨stage0, ?_, stage0_planar⟩
  show ∀ i : Fin 8, stage0.degree i = ([2, 7, 6, 5, 3, 3, 3, 3] : List Nat)[i]
  decide +kernel

theorem predecessor_planaric : Planaric [7, 6, 6, 3, 3, 3, 3, 2, 1] := by
  have h := planaric_attach_leaf planaric_repair 2
  exact (planaric_perm (e:=[7, 6, 6, 3, 3, 3, 3, 2, 1]) (by decide +kernel)).mp h

end SparseBoundary.LeafRepair5

namespace SparseBoundary.LeafRepair6

open Graph MinorSearch

private def realization : Graph 6 := ⟨16895⟩
private def initial : Nat := 0xfeff0001fefffffe
private def catalog : Array (Option Nat) := ((List.range 64).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 6).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 6 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

private theorem core_planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

private def stage0 : Graph 7 := ⟨1063925⟩

private theorem stage0_planar : stage0.Planar :=
  degree_two_extension (G:=stage0) core_planar 0 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem planaric_repair : Planaric [5, 4, 4, 4, 4, 2, 1] := by
  apply (planaric_perm (d:=[2, 5, 4, 4, 4, 4, 1]) (by decide +kernel)).mp
  refine ⟨stage0, ?_, stage0_planar⟩
  show ∀ i : Fin 7, stage0.degree i = ([2, 5, 4, 4, 4, 4, 1] : List Nat)[i]
  decide +kernel

end SparseBoundary.LeafRepair6

namespace SparseBoundary

/-- The five non-universal one-leaf predecessors on the upper layer. -/
theorem leaf_predecessor_repaired {d : List Nat}
    (hd : d ∈ [[1,5,5,4,4,4,3], [1,6,5,5,5,5,3,2,2],
      [1,5,4,4,4,4,4,4], [1,6,6,5,3,3,3,3], [1,7,6,6,3,3,3,3,2]]) :
    Planaric d := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact (planaric_perm (d:=[5,5,4,4,4,3,1]) (by decide)).mp LeafRepair1.predecessor_planaric
  · exact (planaric_perm (d:=[6,5,5,5,5,3,2,2,1]) (by decide)).mp LeafRepair2.predecessor_planaric
  · exact (planaric_perm (d:=[5,4,4,4,4,4,4,1]) (by decide)).mp LeafRepair3.predecessor_planaric
  · exact (planaric_perm (d:=[6,6,5,3,3,3,3,1]) (by decide)).mp LeafRepair4.predecessor_planaric
  · exact (planaric_perm (d:=[7,6,6,3,3,3,3,2,1]) (by decide)).mp LeafRepair5.predecessor_planaric

/-- The only possible first one-leaf predecessor of (4^5,2) when
    maximum-lowering is reversed. -/
theorem lower_leaf_predecessor_repaired : Planaric [1,5,4,4,4,4,2] :=
  (planaric_perm (d:=[5,4,4,4,4,2,1]) (by decide)).mp LeafRepair6.planaric_repair

end SparseBoundary
