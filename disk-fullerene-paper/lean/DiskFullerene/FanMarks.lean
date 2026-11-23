import DiskFullerene.FanBoundary

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

theorem side_index {α} [DecidableEq α] {r : List α} (nd : r.Nodup) {a b} (e : (a,b)∈sides r) :
    next r.length (r.idxOf a)=r.idxOf b := by
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp e; rw [sides_size] at hk; rw [side_at _ _ hk] at eq
  cases eq; simp only [List.Nodup.idxOf_getElem nd]

theorem marks_not_cyclic {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) :
    ¬OnCycle (dualRow G (apex M)) (atSide G (apex M) d.i) (atSide G (apex M) d.j) := by
  let w := apex M; let R := dualRow G w
  have nd := row_nodup G (noRepeatOnSphere G hh) w
  have indices (i : OuterIndex M) : R.idxOf (atSide G w i)=i.val := by rw [atSide_eq]; exact List.Nodup.idxOf_getElem nd i.val _
  have ⟨lt,_,_,⟨a,_,ia,aj⟩,⟨b,bin,bc⟩⟩ := d.proper
  change d.i.val<d.j.val at lt; change d.i.val<a at ia; change a<d.j.val at aj
  change b<M.faces[w.val].length at bin; change b<d.i.val ∨ d.j.val<b at bc
  intro step; rcases step with e|e <;> have eq := side_index nd e <;> change next R.length (R.idxOf _) = R.idxOf _ at eq <;>
    rw [indices,indices] at eq <;> change next (dualRow G w).length _ = _ at eq <;> rw [row_length] at eq <;>
    unfold next at eq <;> split at eq <;> omega

namespace TerminalAnnulus
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

theorem mark_slots (T : TerminalAnnulus d) (hh : 3≤h) {v t : Face M}
    (b : IsBoundary G v) (bt : IsBoundary G t) (vt : t∈dualRow G v)
    (chord : ¬OnCycle (dualRow G (apex M)) v t) :
    ∃ p q : Face M, [apex M,p,q,t].Nodup ∧ [apex M,p,q,t] ⊆ dualRow G v ∧
      (∀ z∈[apex M,p,q,t], z=apex M ∨ IsBoundary G z) ∧ OnCycle (dualRow G (apex M)) v p ∧ OnCycle (dualRow G (apex M)) v q := by
  obtain ⟨p,q,nd,nb,cl,pc,qc⟩ := T.boundarySlots hh b
  have nv : apex M≠t := fun eq=>row_no_loop G hh _ (eq ▸ bt)
  have np : p≠t := fun eq=>chord (eq ▸ pc)
  have nq : q≠t := fun eq=>chord (eq ▸ qc)
  refine ⟨p,q,by simp at nd; simp [nd,nv,np,nq],?_,?_,pc,qc⟩
  · intro z zm; by_cases zt : z=t; exact zt ▸ vt
    apply nb; simp at zm ⊢; grind
  · intro z zm; by_cases zt : z=t; exact .inr (zt ▸ bt)
    apply cl; simp at zm ⊢; grind

theorem mark_other (_T : TerminalAnnulus d) (hh : 3≤h) {v} (mark : v=atSide G (apex M) d.i ∨ v=atSide G (apex M) d.j) :
    ∃ t, IsBoundary G v ∧ IsBoundary G t ∧ t∈dualRow G v ∧ ¬OnCycle (dualRow G (apex M)) v t := by
  have dualNeighbors (G : IsDiskFullerene M h) {e : Edge M} {a b : Face M} (ac : Across (dual G) e a b) : b∈dualRow G a := by
    have f : (dual G e).2∈dualRow G (dual G e).1 := (mem_row_iff G _ _).mpr ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
    rcases ac with eq|eq <;> rw [eq] at f; exact f; exact (dual_adj_symmetric G _ _).mp f
  have dx := dualNeighbors G d.seam.first; have dy := dualNeighbors G d.seam.last.symm; have xy := dualNeighbors G d.seam.middle
  have ch := marks_not_cyclic hh d
  rcases mark with rfl|rfl
  · exact ⟨_,dx,dy,xy,ch⟩
  · exact ⟨_,dy,dx,(dual_adj_symmetric G _ _).mp xy,fun cy=>ch cy.symm⟩

theorem mark_capacity (T : TerminalAnnulus d) (hh : 3≤h) {v} (mark : v=atSide G (apex M) d.i ∨ v=atSide G (apex M) d.j) : (T.touches v).length≤2 := by
  obtain ⟨t,b,bt,nb,ch⟩ := T.mark_other hh mark
  obtain ⟨p,q,nd,sub,cl,_,_⟩ := T.mark_slots hh b bt nb ch
  have cap := T.mixed_degree [_,p,q,t] nd sub cl
  have deg := inner_degree G (show v≠apex M from fun eq=>row_no_loop G hh _ (eq ▸ b))
  simp only [List.length_cons,List.length_nil] at cap; omega

/-- The subdivision vertex cannot be any of the five fan junctions. -/
theorem mid_ne_corner (T : TerminalAnnulus d) (hh : 3≤h) {i u} (mid : (T.fans.arc i).mid=some u) (j : I) : u≠(T.fans.arc j).first := by
  intro eq
  have nd := (T.fans.neighbors i).nodup_iff.mpr (row_nodup G (noRepeatOnSphere G hh) _)
  simp [Arc.word,mid] at nd
  have het : i≠j := by intro ij; subst j; grind
  have prev : i≠before j := by
    intro ib
    have af : after i=j := by rw [ib]; exact (by decide : ∀ j : I, after (before j)=j) j
    have join := T.fans.joined hh i; rw [af] at join; grind
  have table : ∀ a : I, a≠before a := by decide
  have hit₁ : i∈T.touches u := T.meets (by simp [Arc.word,mid])
  have hit₂ : j∈T.touches u := by rw [eq]; exact T.meets (by simp [Arc.word])
  have hit₃ : before j∈T.touches u := by rw [eq]; exact T.previous_meets hh j
  have uniq : [i,j,before j].Nodup := by simp [het,prev,table]
  have large := uniq.length_le_of_subset (l₂:=T.touches u) (by intro a m; simp at m; grind)
  have low := T.mark_capacity hh (T.split_mark hh mid); simp at large; omega

end TerminalAnnulus
end DiskFullerene.EndFans
