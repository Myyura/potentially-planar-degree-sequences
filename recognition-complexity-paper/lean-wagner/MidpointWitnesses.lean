import Transfer
import SparseBoundary.GraphPerm

/-! Explicit stacked witnesses for the two sorted endpoints and a simple
graph on the same thirteen labels with the midpoint degree list. -/
namespace Recognition.MidpointWitnesses
open SparseBoundary Recognition.SourceMap Recognition.SourceBridge

private theorem from_mesh (M : Mesh) (ds : List Nat) (stacked : Stacked M)
    (names : ∀ i, M.vertex i ↔ i<ds.length)
    (degrees : ∀ i : Fin ds.length, (M.neighbors i.val).length=ds[i.val]) :
    Planaric ds := by
  obtain ⟨B⟩ := stacked_bridge stacked
  let R : Layers.Model ds := {
    V := B.V, map := B.map, vertices := B.enum, label := B.label,
    inj := fun _ _ h => B.inj h,
    hits := fun i => (names i).symm.trans (B.hits i),
    value := fun x => by
      let i : Fin ds.length := ⟨B.label x,(names _).mp ((B.hits _).mpr ⟨x,rfl⟩)⟩
      rw [B.degree_eq (regular stacked), List.getElem?_eq_getElem i.isLt]
      simpa [i] using degrees i }
  exact ⟨Transfer.graph R,Transfer.graph_realizes R,
    BipartiteMinor.stacked_planar R B.origin _ (Transfer.same_edges R)⟩

private def low4 := stack tetra ⟨0,1,3⟩ 4
private theorem low4_ok : Stacked low4 := by
  apply Stacked.insert .tetra
  · simp +decide [tetra]
  · simp +decide [tetra]
private def low5 := stack low4 ⟨1,3,4⟩ 5
private theorem low5_ok : Stacked low5 := by
  apply Stacked.insert low4_ok
  · simp +decide [low4,stack,tetra]
  · simp +decide [low4,stack,tetra]
private def low6 := stack low5 ⟨1,3,5⟩ 6
private theorem low6_ok : Stacked low6 := by
  apply Stacked.insert low5_ok
  · simp +decide [low5,low4,stack,tetra]
  · simp +decide [low5,low4,stack,tetra]
private def low7 := stack low6 ⟨1,3,6⟩ 7
private theorem low7_ok : Stacked low7 := by
  apply Stacked.insert low6_ok
  · simp +decide [low6,low5,low4,stack,tetra]
  · simp +decide [low6,low5,low4,stack,tetra]
private def low8 := stack low7 ⟨3,6,7⟩ 8
private theorem low8_ok : Stacked low8 := by
  apply Stacked.insert low7_ok
  · simp +decide [low7,low6,low5,low4,stack,tetra]
  · simp +decide [low7,low6,low5,low4,stack,tetra]
private def low9 := stack low8 ⟨3,7,8⟩ 9
private theorem low9_ok : Stacked low9 := by
  apply Stacked.insert low8_ok
  · simp +decide [low8,low7,low6,low5,low4,stack,tetra]
  · simp +decide [low8,low7,low6,low5,low4,stack,tetra]
private def low10 := stack low9 ⟨3,6,8⟩ 10
private theorem low10_ok : Stacked low10 := by
  apply Stacked.insert low9_ok
  · simp +decide [low9,low8,low7,low6,low5,low4,stack,tetra]
  · simp +decide [low9,low8,low7,low6,low5,low4,stack,tetra]
private def low11 := stack low10 ⟨3,5,6⟩ 11
private theorem low11_ok : Stacked low11 := by
  apply Stacked.insert low10_ok
  · simp +decide [low10,low9,low8,low7,low6,low5,low4,stack,tetra]
  · simp +decide [low10,low9,low8,low7,low6,low5,low4,stack,tetra]
private def low12 := stack low11 ⟨0,3,4⟩ 12
private theorem low12_ok : Stacked low12 := by
  apply Stacked.insert low11_ok
  · simp +decide [low11,low10,low9,low8,low7,low6,low5,low4,stack,tetra]
  · simp +decide [low11,low10,low9,low8,low7,low6,low5,low4,stack,tetra]

theorem low_planaric : Planaric [12,7,7,5,5,5,5,5,3,3,3,3,3] := by
  apply (planaric_perm (d := [5,7,3,12,5,5,7,5,5,3,3,3,3]) (by decide +kernel)).mp
  apply from_mesh low12 _ low12_ok
  · intro i
    simp only [low12,low11,low10,low9,low8,low7,low6,low5,low4,stack,tetra,List.length_cons,List.length_nil]
    omega
  · decide +kernel

private def high4 := stack tetra ⟨0,1,3⟩ 4
private theorem high4_ok : Stacked high4 := by
  apply Stacked.insert .tetra
  · simp +decide [tetra]
  · simp +decide [tetra]
private def high5 := stack high4 ⟨1,3,4⟩ 5
private theorem high5_ok : Stacked high5 := by
  apply Stacked.insert high4_ok
  · simp +decide [high4,stack,tetra]
  · simp +decide [high4,stack,tetra]
private def high6 := stack high5 ⟨0,3,4⟩ 6
private theorem high6_ok : Stacked high6 := by
  apply Stacked.insert high5_ok
  · simp +decide [high5,high4,stack,tetra]
  · simp +decide [high5,high4,stack,tetra]
private def high7 := stack high6 ⟨0,3,6⟩ 7
private theorem high7_ok : Stacked high7 := by
  apply Stacked.insert high6_ok
  · simp +decide [high6,high5,high4,stack,tetra]
  · simp +decide [high6,high5,high4,stack,tetra]
private def high8 := stack high7 ⟨3,6,7⟩ 8
private theorem high8_ok : Stacked high8 := by
  apply Stacked.insert high7_ok
  · simp +decide [high7,high6,high5,high4,stack,tetra]
  · simp +decide [high7,high6,high5,high4,stack,tetra]
private def high9 := stack high8 ⟨0,3,7⟩ 9
private theorem high9_ok : Stacked high9 := by
  apply Stacked.insert high8_ok
  · simp +decide [high8,high7,high6,high5,high4,stack,tetra]
  · simp +decide [high8,high7,high6,high5,high4,stack,tetra]
private def high10 := stack high9 ⟨0,3,9⟩ 10
private theorem high10_ok : Stacked high10 := by
  apply Stacked.insert high9_ok
  · simp +decide [high9,high8,high7,high6,high5,high4,stack,tetra]
  · simp +decide [high9,high8,high7,high6,high5,high4,stack,tetra]
private def high11 := stack high10 ⟨3,9,10⟩ 11
private theorem high11_ok : Stacked high11 := by
  apply Stacked.insert high10_ok
  · simp +decide [high10,high9,high8,high7,high6,high5,high4,stack,tetra]
  · simp +decide [high10,high9,high8,high7,high6,high5,high4,stack,tetra]
private def high12 := stack high11 ⟨0,3,10⟩ 12
private theorem high12_ok : Stacked high12 := by
  apply Stacked.insert high11_ok
  · simp +decide [high11,high10,high9,high8,high7,high6,high5,high4,stack,tetra]
  · simp +decide [high11,high10,high9,high8,high7,high6,high5,high4,stack,tetra]

theorem high_planaric : Planaric [12,9,5,5,5,5,5,5,3,3,3,3,3] := by
  apply (planaric_perm (d := [9,5,3,12,5,3,5,5,3,5,5,3,3]) (by decide +kernel)).mp
  apply from_mesh high12 _ high12_ok
  · intro i
    simp only [high12,high11,high10,high9,high8,high7,high6,high5,high4,stack,tetra,List.length_cons,List.length_nil]
    omega
  · decide +kernel

private def rows : List (List Nat) := [
  [1,2,3,4,5,6,7,8,9,10,11,12],
  [0,2,3,5,6,7,8,12],
  [0,1,3,4,8,9],
  [0,1,2,4,9],
  [0,2,3,5,10],
  [0,1,4,6,10],
  [0,1,5,7,11],
  [0,1,6,11,12],
  [0,1,2],
  [0,2,3],
  [0,4,5],
  [0,6,7],
  [0,1,7]]

theorem middle_graphic :
    ∃ G : Graph 13, G.Realizes [12,8,6,5,5,5,5,5,3,3,3,3,3] := by
  let G := Graph.ofRelation (fun i j : Fin 13 => (rows[i.val]!).contains j.val)
  refine ⟨G,?_⟩
  unfold Graph.Realizes
  decide +revert +kernel

end Recognition.MidpointWitnesses
