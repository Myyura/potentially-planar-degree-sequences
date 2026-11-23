import DiskFullerene.FanMarks

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

private theorem face_at {M} {G : IsDiskFullerene M h} {w x y} (S : TriangleSide G w x y) (B : Bool) {f : Face M}
    (nf : f≠w ∧ f≠x ∧ f≠y) {u : Fin M.ord} (m : u.val∈M.faces[f.val]) : faceSide S B f=vertexSide S B u := by
  classical
  have src : S.color u.val ↔ S.part.left u := ⟨fun ⟨_,s⟩=>s,fun s=>⟨u.isLt,s⟩⟩
  simp [faceSide,vertexSide,nf,(S.color_at nf m).trans src]

private theorem adj_data {M} (G : IsDiskFullerene M h) {x y : Face M} (adj : y∈dualRow G x) :
    ∃ e : Edge M, Across (dual G) e x y ∧ (primal G e).1.val∈M.faces[x.val] := by
  obtain ⟨z,hx,hy⟩ := (mem_row_iff G x y).mp adj; obtain ⟨e,orient⟩ := repr_dart G (incident_dart G hx)
  refine ⟨e,crossTable G orient (Or.inl ⟨hx,hy⟩),?_⟩; change (endpoints e).1∈_
  rcases orient with eq|eq <;> rw [eq]; exact (sideEnds hx).1; exact (sideEnds hx).2

private theorem onBoundary_regular {M} {G : IsDiskFullerene M h} (hh : 3≤h) {d : EndPiece M G} {r z : Face M}
    (rb : IsBoundary G r) (zb : IsBoundary G z) (near : z∈dualRow G r) (chosen : faceSide d.seam d.side z=true) :
    OnCycle (dualRow G (apex M)) r z := by
  classical
  let S:=d.seam; let B:=d.side
  have nc : z≠apex M ∧ z≠atSide G (apex M) d.i ∧ z≠atSide G (apex M) d.j := of_decide_eq_true (Bool.and_eq_true_iff.mp chosen).1
  obtain ⟨e,ac,zm⟩ := adj_data G ((dual_adj_symmetric G _ _).mp near)
  have inside : vertexSide S B (primal G e).1=true := (face_at S B nc zm).symm.trans chosen
  rcases d.terminal.seam_or_cycle hh S B rb zb ac.symm (Or.inl inside) with Cy|ep
  · exact Cy
  · subst e; rcases ac with a|a <;> rcases S.middle with b|b <;> have both := Prod.mk.inj (a.symm.trans b) <;> grind

private theorem seam_info {M} {G : IsDiskFullerene M h} (d : EndPiece M G) {r : Face M} (mark : r=atSide G (apex M) d.i ∨ r=atSide G (apex M) d.j) :
    ∃ e : Edge M, Across (dual G) e r (apex M) ∧ ThreeEdges d.seam.wx d.seam.xy d.seam.yw e := by
  rcases mark with rfl|rfl; exact ⟨_,d.seam.first.symm,.inl rfl⟩; exact ⟨_,d.seam.last,.inr (.inr rfl)⟩

/-- At either marked endpoint exactly one original boundary vertex is
strictly on the chosen side of its seam; selected strict boundary
neighbors cannot be joined to it by any other chord. -/
theorem boundary_contribution {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) {r : Face M}
    (mark : r=atSide G (apex M) d.i ∨ r=atSide G (apex M) d.j) :
    ∃ v, IsBoundary G v ∧ v∈dualRow G r ∧ faceSide d.seam d.side v=true ∧
      ∀ z, IsBoundary G z → z∈dualRow G r → faceSide d.seam d.side z=true → z=v := by
  classical
  let S:=d.seam; let B:=d.side; let w:=apex M; let x:=atSide G w d.i; let y:=atSide G w d.j
  let C:=dualRow G w
  have cb := boundary_cycle G hh
  have b (i : OuterIndex M) : IsBoundary G (atSide G w i) := by unfold IsBoundary; rw [atSide_eq]; exact List.getElem_mem _
  have rb : r∈C := by rcases mark with rfl|rfl; exact b d.i; exact b d.j
  obtain ⟨p,pC,q,qC,pq,pr,rq,only⟩ := cycle_at cb.1 (by omega) rb
  have seamNot := marks_not_cyclic hh d
  change ¬OnCycle C x y at seamNot
  have nongood {z} (zc : z∈C) (rz : OnCycle C r z) : z≠w ∧ z≠x ∧ z≠y := by
    refine ⟨fun eq=>row_no_loop G hh w (show w∈C from eq ▸ zc),?_,?_⟩
    · intro eq; subst z; rcases mark with m|m
      · change r=x at m; subst r; rcases rz with e|e <;> exact row_no_loop G hh _ (cyclic_link G _ e)
      · change r=y at m; subst r; exact seamNot rz.symm
    · intro eq; subst z; rcases mark with m|m
      · change r=x at m; subst r; exact seamNot rz
      · change r=y at m; subst r; rcases rz with e|e <;> exact row_no_loop G hh _ (cyclic_link G _ e)
  have np := nongood pC (.inr pr); have nq := nongood qC (.inl rq)
  obtain ⟨e,E,seam⟩ := seam_info d mark
  have corner {a} (step : OnCycle (dualRow G a) r w) : ∃ v : Fin M.ord,
      (v=(primal G e).1 ∨ v=(primal G e).2) ∧ v.val∈M.faces[a.val] ∧ ∀ f : Face M, v.val∈M.faces[f.val] → f=a ∨ f=r ∨ f=w := by
    rcases step with step|step
    · obtain ⟨k,v,ac,en,am,fs⟩ := cornerEdge G step; have ke := uniqueAcross G hh ac E; exact ⟨v,ke ▸ en,am,fs⟩
    · obtain ⟨k,v,ac,en,am,fs⟩ := cornerEdge G step; have ke := uniqueAcross G hh ac.symm E; exact ⟨v,ke ▸ en,am,fun f m=>by have := fs f m; grind⟩
  obtain ⟨u,ue,up,fu⟩ := corner (.inl (turn_triangle G pr).1)
  obtain ⟨v,ve,vq,_⟩ := corner (.inr (turn_triangle G rq).2)
  have uv : u≠v := by intro eq; subst v; have := fu q vq; rcases mark with m|m <;> change r=_ at m <;> grind
  have flip := (S.part.crosses e).mp seam
  have unequal : vertexSide S B u ≠ vertexSide S B v := by
    rcases ue with ua|ua <;> rcases ve with vb|vb <;> rw [ua,vb] at uv ⊢ <;> first | contradiction | simp only [vertexSide] <;> by_cases cp : S.part.left (primal G e).1 <;> by_cases cq : S.part.left (primal G e).2 <;> cases B <;> simp_all
  have fs : faceSide S B p≠faceSide S B q := by rw [face_at S B np up,face_at S B nq vq]; exact unequal
  have ap := (dual_adj_symmetric G _ _).mp (cyclic_link G _ pr); have aq := cyclic_link G _ rq
  have opt (z : Face M) (zb : IsBoundary G z) (zr : z∈dualRow G r) (pick : faceSide S B z=true) : z=p ∨ z=q :=
    only z (onBoundary_regular hh rb zb zr pick)
  cases l : faceSide S B p <;> cases k : faceSide S B q <;> first | exact False.elim (fs (l.trans k.symm)) | exact ⟨p,pC,ap,l,fun z zb zr s=>by rcases opt z zb zr s with o|rfl; exact o; grind⟩ | exact ⟨q,qC,aq,k,fun z zb zr s=>by rcases opt z zb zr s with rfl|o; grind; exact o⟩

end DiskFullerene.EndFans
