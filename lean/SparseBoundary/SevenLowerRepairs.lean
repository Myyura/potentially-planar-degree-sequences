import SparseBoundary.LeafRepairs
import SparseBoundary.Repair3
import SparseBoundary.GraphWeighted
import SparseBoundary.SevenUniversal

namespace SparseBoundary.Graph

/-- Deleting an arbitrary set of edges preserves forbidden-minor planarity. -/
theorem planar_subgraph {G H : Graph n} (hp : H.Planar)
    (le : ∀ i j, G.adj i j = true → H.adj i j = true) : G.Planar := by
  have promote {k : Nat} {R : Fin k → Fin k → Bool} (irr : ∀ i, R i i=false)
      {s} (model : G.minorTest R s=true) : ∃ b, H.minorTest R b=true := by
    apply transfer_minor irr s model id (fun i j h => Or.inr (le i j h))
    intro i j ne x hx y hy he
    change x=y at he
    subst y
    have row := List.all_eq_true.mp model i (List.mem_finRange i)
    have cell := List.all_eq_true.mp (Bool.and_eq_true_iff.mp row).2 j (List.mem_finRange j)
    have dis := (Bool.or_eq_true_iff.mp (Bool.and_eq_true_iff.mp cell).1).resolve_left (by simp [ne])
    have sep : ∀ u∈s i, u∉s j := by simpa [disjoint,List.all_eq_true] using dis
    exact sep x hx hy
  exact ⟨fun ⟨_,m⟩ => hp.1 (promote (by decide) m),fun ⟨_,m⟩ => hp.2 (promote (by decide) m)⟩

end SparseBoundary.Graph

namespace SparseBoundary.SevenLower
open Graph

private def support (i : Fin 5) : Graph 7 :=
  match i with
  | 0 => LeafRepair4.doubleFan.eraseEdge 1 2
  | 1 => SevenUniversal.Layer0.wheel.eraseEdge 3 4
  | 2 => Repair3.sevenGraph.eraseEdge 2 4
  | 3 => LeafRepair3.oneThreeBase.eraseEdge 1 4
  | 4 => LeafRepair3.oneThreeBase.eraseEdge 0 1

private def original (i : Fin 5) : Graph 7 :=
  match i with
  | 0 => LeafRepair4.doubleFan
  | 1 => SevenUniversal.Layer0.wheel
  | 2 => Repair3.sevenGraph
  | 3 | 4 => LeafRepair3.oneThreeBase

private theorem base_planar (i : Fin 5) : (support i).Planar := by
  have all : ∀ j : Fin 5, ∀ u v : Fin 7, (support j).adj u v = true → (original j).adj u v = true := by decide +kernel
  apply planar_subgraph (H:=original i) _ (all i)
  match i with
  | 0 => exact LeafRepair4.doubleFan_planar
  | 1 => exact SevenUniversal.Layer0.wheel_planar
  | 2 => exact Repair3.sevenGraph_planar
  | 3 | 4 => exact LeafRepair3.oneThreeBase_planar

theorem five_threes (t : Nat) :
    Planaric ([6+t,5+t,3,3,3,3,3] ++ List.replicate t 2) := by
  let H := support 0
  let E : List (Fin 7 × Fin 7) := List.replicate t (0,1)
  have good e (he : e∈E) : H.adj e.1 e.2=true := by
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp he; decide +kernel
  have p := expanded_planaric (base_planar 0) E good
  have inc (i : Fin 7) : increments E i=(if pairRow 0 1 i then t else 0) := List.countP_replicate
  have out : List.ofFn (fun i => H.degree i + increments E i)=[6+t,5+t,3,3,3,3,3] := by
    change [H.degree 0+increments E 0,H.degree 1+increments E 1,H.degree 2+increments E 2,
      H.degree 3+increments E 3,H.degree 4+increments E 4,H.degree 5+increments E 5,H.degree 6+increments E 6]=_
    have dg : H.degree 0=6 ∧ H.degree 1=5 ∧ H.degree 2=3 ∧ H.degree 3=3 ∧ H.degree 4=3 ∧
        H.degree 5=3 ∧ H.degree 6=3 := by decide +kernel
    obtain ⟨d0,d1,d2,d3,d4,d5,d6⟩ := dg
    simp only [inc,d0,d1,d2,d3,d4,d5,d6]
    rfl
  change Planaric (List.replicate E.length 2 ++ List.ofFn (fun i => H.degree i+increments E i)) at p
  rw [out,show E.length=t from List.length_replicate] at p
  exact (planaric_perm List.perm_append_comm).mp p

private def targets : List (List Nat) := [
  [5,5,4,3,3,3,3], [5,4,4,4,3,3,3], [4,4,4,4,4,3,3], [4,4,4,4,4,4,4,2],
  [6,5,5,3,3,3,3,2], [6,6,6,3,3,3,3,2,2] ]

theorem repair (i : Fin 6) : Planaric targets[i] := by
  let data : List (Fin 5 × List (Fin 7 × Fin 7)) := [
    (2,[]),(3,[]),(4,[]),(4,[(1,6)]),(1,[(1,2)]),(1,[(1,2),(1,2)])]
  let h := fun j : Fin 6 => support data[j].1
  let E := fun j : Fin 6 => data[j].2
  have good : ∀ j, ∀ e ∈ E j, (h j).adj e.1 e.2 = true := by decide +kernel
  have out := expanded_planaric (base_planar data[i].1) (E i) (good i)
  have per : ∀ j : Fin 6, (List.replicate (E j).length 2 ++
      List.ofFn (fun v => (h j).degree v + increments (E j) v)).Perm targets[j] := by decide +kernel
  exact (planaric_perm (per i)).mp out

end SparseBoundary.SevenLower
