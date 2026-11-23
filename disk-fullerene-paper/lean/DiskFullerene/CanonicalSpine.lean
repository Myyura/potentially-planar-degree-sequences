import DiskFullerene.TraceFresh
import DiskFullerene.CapEmbedding

namespace DiskFullerene.StripFresh.Trace
open Dual EndLabels EndEuler Separation Strip
variable {M : MapData} {G : IsDiskFullerene M h}

/-- Original face labels in chronological order, including the marked
edge at which the traversal starts. -/
def word {x y a b} (t : Trace G x y a b) := x::y::t.newVertices

theorem word_len {x y a b} (t : Trace G x y a b) : t.word.length=t.moves.length+2 := by
  simp [word,t.length_eq,t.moves_count]

theorem final_pair {x y a b k} (t : Trace G x y a b) (right : t.moves=List.replicate k .right) :
    t.word[k]?=some a ∧ t.word[k+1]?=some b := by
  induction t generalizing k with
  | done => cases k <;> simp [moves,word,newVertices,List.replicate_succ] at *
  | keepFirst e t ih => cases k <;> simp [moves,List.replicate_succ] at right
  | @keepSecond x y z a b e t ih =>
    cases k with
    | zero => simp [moves] at right
    | succ k =>
      have r : t.moves=List.replicate k .right := by simpa [moves,List.replicate_succ] using right
      exact ih r

private theorem edge_triangle (hh : 3≤h) {u : Fin M.ord} {f g : Face M}
    (hit : f∈triangle u) (other : g∈triangle u) (ne : f≠g) : g∈dualRow G f := by
  obtain ⟨a,b,C,_,_,_,faces⟩ := corners_at G hh ((mem_triangle _ _).mp hit)
  obtain ⟨j,lt,eq⟩ := List.mem_iff_getElem.mp C.step; rw [sides_size] at lt; rw [side_at _ _ lt] at eq
  rcases (faces g).mp ((mem_triangle _ _).mp other) with bad|rfl|rfl
  · exact False.elim (ne bad.symm)
  · exact (Prod.mk.inj eq).1 ▸ List.getElem_mem _
  · exact (Prod.mk.inj eq).2 ▸ List.getElem_mem _

/-- Every positive edge of the canonical distance-two strip comes from
an actual triangle or from the initial seam, for all strip lengths. -/
theorem word_edges (hh : 3≤h) {x y a b k} (t : Trace G x y a b) (right : t.moves=List.replicate k .right)
    (verified : t.records) (nd : t.word.Nodup) (initial : y∈dualRow G x)
    (i j : Nat) (hi : i<t.word.length) (hj : j<t.word.length) (ed : Construction.stripEdge i j=true) :
    t.word[j]∈dualRow G t.word[i] := by
  have nums : i≠j ∧ i≤j+2 ∧ j≤i+2 := of_decide_eq_true ed
  induction t generalizing k i j with
  | done x y =>
    change i<2 at hi; change j<2 at hj
    have pairs : i=0 ∧ j=1 ∨ i=1 ∧ j=0 := by omega
    rcases pairs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩; exact initial; exact (dual_adj_symmetric G _ _).mp initial
  | keepFirst e t ih => cases k <;> simp [moves,List.replicate_succ] at right
  | @keepSecond x y z a b e t ih =>
    cases k with
    | zero => simp [moves] at right
    | succ k =>
      have r : t.moves=List.replicate k .right := by simpa [moves,List.replicate_succ] using right
      obtain ⟨faces,rec⟩ := verified
      change (x::y::z::t.newVertices).Nodup at nd
      have zx : x≠z := fun eq=>(List.nodup_cons.mp nd).1 (by simp [eq])
      have zy : y≠z := fun eq=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [eq])
      have xv := (faces x).mpr (by simp); have yv := (faces y).mpr (by simp); have zv := (faces z).mpr (by simp)
      have xz := edge_triangle (G:=G) hh xv zv zx; have yz := edge_triangle (G:=G) hh yv zv zy
      cases i with
      | zero =>
        have only : j=1 ∨ j=2 := by omega
        rcases only with rfl|rfl; exact initial; exact xz
      | succ i => cases j with
        | zero =>
          have only : i=0 ∨ i=1 := by omega
          rcases only with rfl|rfl; exact (dual_adj_symmetric G _ _).mp initial; exact (dual_adj_symmetric G _ _).mp xz
        | succ j =>
          have vi : i<t.word.length := Nat.lt_of_succ_lt_succ hi
          have vj : j<t.word.length := Nat.lt_of_succ_lt_succ hj
          have good : i≠j ∧ i≤j+2 ∧ j≤i+2 := by omega
          exact ih r rec (List.nodup_cons.mp nd).2 yz i j vi vj (decide_eq_true good) good

/-- Original two start labels and every newly introduced vertex lie on
the outer cycle. A new label comes with a witnessing middle triangle. -/
theorem new_on_triangle {x y a b} (t : Trace G x y a b) {f} (m : f∈t.newVertices) :
    ∃ u∈t.triangles, f∈triangle u := by
  induction t with
  | done => simp [newVertices] at m
  | @keepFirst x y z a b edge tail ih =>
    rcases List.mem_cons.mp m with rfl|mem
    · exact ⟨edge.label,by simp [triangles],edge.last⟩
    · obtain ⟨u,inTail,fu⟩ := ih mem; exact ⟨u,by simp [triangles,inTail],fu⟩
  | @keepSecond x y z a b edge tail ih =>
    rcases List.mem_cons.mp m with rfl|mem
    · exact ⟨edge.label,by simp [triangles],edge.last⟩
    · obtain ⟨u,inTail,fu⟩ := ih mem; exact ⟨u,by simp [triangles,inTail],fu⟩

private theorem arc_end {C : List α} {p q : α} (edge : OnCycle C p q) : q∈C := by
  rcases edge with e|e <;> obtain ⟨j,lt,eq⟩ := List.mem_iff_getElem.mp e <;> rw [sides_size] at lt <;> rw [side_at _ _ lt] at eq
  · exact (Prod.mk.inj eq).2 ▸ List.getElem_mem _
  · exact (Prod.mk.inj eq).1 ▸ List.getElem_mem _

theorem word_boundary {x y a b} (t : Trace G x y a b) (bx : IsBoundary G x) (by' : IsBoundary G y) :
    t.word ⊆ dualRow G (apex M) := by
  have all : ∀ z∈t.newVertices, IsBoundary G z := by
    intro z hz; induction t with
    | done => simp [newVertices] at hz
    | keepFirst e t ih => rcases List.mem_cons.mp hz with rfl|m; exact arc_end e.cyclic; exact ih bx (arc_end e.cyclic) m
    | keepSecond e t ih => rcases List.mem_cons.mp hz with rfl|m; exact arc_end e.cyclic; exact ih by' (arc_end e.cyclic) m
  intro f hf; rcases List.mem_cons.mp hf with rfl|hf; exact bx; rcases List.mem_cons.mp hf with rfl|hf; exact by'; exact all _ hf

end DiskFullerene.StripFresh.Trace
