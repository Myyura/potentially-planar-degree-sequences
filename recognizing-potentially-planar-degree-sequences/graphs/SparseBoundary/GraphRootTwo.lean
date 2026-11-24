import SparseBoundary.GraphSmooth
import SparseBoundary.GraphDeletion

namespace SparseBoundary.Graph

/-- Every labelled degree-two root is exactly the added two-edge path on
    the graph induced by the other vertices, whether or not its ends meet. -/
theorem degree_two_root {G : Graph (n+1)} (deg : G.degree 0=2) :
    ∃ a b : Fin n, a≠b ∧ G=(G.restrict Fin.succ).parallelPath a b := by
  let r := fun i : Fin n => G.adj 0 i.succ
  let nbr := (List.finRange n).filter r
  have nr : nbr.length=2 := by
    simpa [degree,List.finRange_succ,List.filter_map,r,nbr,Function.comp_def] using deg
  have shp {xs : List (Fin n)} (len : xs.length=2) : ∃ a b, xs=[a,b] := by
    match xs with
    | [a,b] => exact ⟨a,b,rfl⟩
    | [] | [_] | _::_::_::_ => simp at len
  obtain ⟨a,b,shape⟩ := shp nr
  have nod : nbr.Nodup := List.Pairwise.filter _ (List.nodup_finRange n)
  rw [shape] at nod
  have row (v : Fin n) : r v=pairRow a b v := by
    apply Bool.eq_iff_iff.mpr
    have h : v∈nbr ↔ v=a ∨ v=b := by simp [shape]
    simpa [nbr,List.mem_finRange,pairRow] using h
  refine ⟨a,b,by simpa using nod,eq_of_adj ?_⟩
  intro i j
  refine Fin.cases ?_ (fun v => ?_) i <;> refine Fin.cases ?_ (fun w => ?_) j
  · simp
  · simpa [parallelPath,incident,r] using row w
  · simpa [parallelPath,incident,G.adj_comm v.succ 0,r] using row v
  · simp [parallelPath,incident]

private def completeRel (K : Graph n) (a b i j : Fin n) :=
  K.adj i j || ((i == a && j == b) || (i == b && j == a))

private def completeEdge (K : Graph n) (a b : Fin n) := ofRelation (completeRel K a b)

private theorem complete_adj {K : Graph n} {a b : Fin n} (hn : a≠b) (i j : Fin n) :
    (completeEdge K a b).adj i j=completeRel K a b i j := by
  apply adj_ofRelation
  · intro u v; simp only [completeRel,K.adj_comm u v]; grind
  · intro i; simp [completeRel]; grind

/-- Undoing a subdivision preserves Wagner planarity. -/
theorem unsplit_planar {H : Graph n} {a b : Fin n} (edge : H.adj a b=true)
    (hp : (H.subdivide a b).Planar) : H.Planar := by
  apply contract_planar hp a
  · simp [subdivide,incident,pairRow]
  intro u v he
  by_cases old : (H.eraseEdge a b).adj u v=true
  · exact ⟨u.succ,Or.inl rfl,v.succ,Or.inl rfl,by simpa [subdivide,incident] using old⟩
  · have key : (u=a ∧ v=b) ∨ (u=b ∧ v=a) := by
      simp [erase_adj,eraseRel,he] at old; grind
    rcases key with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨0,Or.inr ⟨rfl,rfl⟩,v.succ,Or.inl rfl,by simp [subdivide,incident,pairRow]⟩
    · exact ⟨u.succ,Or.inl rfl,0,Or.inr ⟨rfl,rfl⟩,by simp [subdivide,incident,pairRow]⟩

/-- Restore the missing edge at a suppressed vertex with nonadjacent ends. -/
theorem restored_edge {K : Graph n} {a b : Fin n} (hn : a≠b) (no : K.adj a b=false)
    (hp : (K.parallelPath a b).Planar) :
    ∃ H : Graph n, H.Planar ∧ H.adj a b=true ∧ H.subdivide a b=K.parallelPath a b ∧
      ∀ i j, K.adj i j=true → H.adj i j=true := by
  let H := completeEdge K a b
  have edge : H.adj a b=true := by simp [H,complete_adj hn,completeRel]
  have erase : H.eraseEdge a b=K := by
    apply eq_of_adj
    intro i j
    simp only [erase_adj,H,eraseRel,complete_adj hn,completeRel]
    have flip := (K.adj_comm b a).trans no
    by_cases h : (i=a ∧ j=b) ∨ (i=b ∧ j=a)
    · rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp_all
    · grind
  have eqn : H.subdivide a b=K.parallelPath a b := by simp [subdivide,parallelPath,erase]
  exact ⟨H,unsplit_planar edge (eqn ▸ hp),edge,eqn,fun i j he => by
    simp [H,complete_adj hn,completeRel,he]⟩

/-- A degree-two vertex whose ends are nonadjacent can be suppressed,
    preserving both ordinary simplicity and planarity and all old degrees. -/
theorem smooth_root {K : Graph n} {a b : Fin n} (hn : a≠b) (no : K.adj a b=false)
    (hp : (K.parallelPath a b).Planar) :
    ∃ H : Graph n, H.Planar ∧ ∀ i : Fin n, H.degree i=(K.parallelPath a b).degree i.succ := by
  obtain ⟨H,hp,edge,eqn,_⟩ := restored_edge hn no hp
  refine ⟨H,hp,fun i => ?_⟩
  rw [← eqn,subdivide_old_degree edge]

end SparseBoundary.Graph
