import DiskFullerene.TerminalRuns

namespace DiskFullerene.Dual
open Dissection EndEuler Separation

abbrev OuterIndex (M : MapData) := Fin M.faces[(apex M).val].length

/-- A selected terminal component with its marked seam and original
outer-link indices. 'diagonal' excludes consecutive boundary neighbors. -/
structure EndPiece (M : MapData) (G : IsDiskFullerene M h) where
  i : OuterIndex M
  j : OuterIndex M
  proper : diagonal (· < M.faces[(apex M).val].length) ⟨i.val,j.val⟩
  seam : TriangleSide G (apex M) (atSide G (apex M) i) (atSide G (apex M) j)
  side : Bool
  terminal : TerminalHalf G (vertexSide seam side)

theorem EndPiece.of_half {M} {G : IsDiskFullerene M h} {p} (P : TerminalHalf G p) :
    ∃ e : EndPiece M G, p=vertexSide e.seam e.side := by
  classical
  obtain ⟨c,hc,i,j,ci,cj,S,B,cs⟩ := P.1
  obtain ⟨_,_,_,_,di,_⟩ := (mem_chords G c).mp hc
  have eq : c=⟨i.val,j.val⟩ := by cases c; simp_all
  have labels : p=vertexSide S B := by
    funext v
    have := cs v
    cases hp : p v <;> cases B <;> simp_all [vertexSide]
  refine ⟨⟨i,j,eq ▸ di,S,B,labels ▸ P⟩,labels⟩

theorem two_pieces {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : HasChord G) :
    ∃ d e : EndPiece M G, ∀ v, ¬(vertexSide d.seam d.side v=true ∧ vertexSide e.seam e.side v=true) := by
  obtain ⟨_,_,P,Q,apart⟩ := two_terminal_ends G hh hc
  obtain ⟨d,rfl⟩ := EndPiece.of_half P
  obtain ⟨e,rfl⟩ := EndPiece.of_half Q
  exact ⟨d,e,apart⟩

theorem EndPiece.open_vertex {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) :
    ∃ b ∈ dualRow G (apex M), faceSide d.seam d.side b=true := by
  classical
  let w := apex M
  let F := M.faces[w.val]
  let N := atSide G w
  let S := d.seam
  let B := d.side
  let i := d.i; let j := d.j
  have adj (k : OuterIndex M) : N k ∈ dualRow G w := by dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
  have away (k : OuterIndex M) : N k≠w := fun eq => row_no_loop G hh _ (eq ▸ adj k)
  let f := primalLabelSide S B
  have pick (k : OuterIndex M) (one : k=i ∨ k=j) : ∃ l : Fin F.length,
      (l.val=k.val ∨ l.val=next F.length k.val) ∧ f F[l.val]=true := by
    have flip := (around_changes hh S (Ne.symm (away i)) (away j) k).mpr
      (by rcases one with rfl|rfl <;> simp [i,j])
    have desc := side_at F k.val k.isLt
    change sideDart M w k = _ at desc
    rw [desc] at flip
    simp only at flip
    let m : Fin F.length := ⟨next F.length k.val,next_bound k.isLt⟩
    by_cases first : f F[k.val]=true
    · exact ⟨k,Or.inl rfl,first⟩
    · refine ⟨m,Or.inr rfl,?_⟩
      change f (F[next F.length k.val]'(next_bound k.isLt))=true
      have changeSide {A C : Prop} [Decidable A] [Decidable C] (t : Bool)
          (flip : ¬(A ↔ C)) (off : (decide A == t)≠true) : (decide C == t)=true := by
        by_cases a : A <;> by_cases c : C <;> cases t <;> simp_all
      exact changeSide B flip first
  obtain ⟨a,ai,fa⟩ := pick i (Or.inl rfl)
  obtain ⟨b,bj,fb⟩ := pick j (Or.inr rfl)
  have ⟨lt,_,_,⟨mid,_,mi,mj⟩,⟨other,ofin,pair⟩⟩ := d.proper
  change i.val<j.val at lt
  change i.val<mid at mi
  change mid<j.val at mj
  change other<F.length at ofin
  change other<i.val ∨ j.val<other at pair
  have ib : i.val<F.length := i.isLt
  have jb : j.val<F.length := j.isLt
  have ij : a.val≠b.val := by
    unfold next at ai bj
    split at ai <;> split at bj <;> omega
  have nn := List.all_eq_true.mp G.faceOrbits F (List.getElem_mem w.isLt)
  have nd : F.Nodup := of_decide_eq_true (Bool.and_eq_true_iff.mp nn).1
  have verts : F[a.val]≠F[b.val] := fun eq => ij (index_eq nd a.isLt b.isLt eq)
  have n2 : [F[a.val],F[b.val]].Nodup := by simp [verts]
  have m2 : [F[a.val],F[b.val]] ⊆ F.filter f := by
    intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl
    · exact List.mem_filter.mpr ⟨List.getElem_mem a.isLt,fa⟩
    · exact List.mem_filter.mpr ⟨List.getElem_mem b.isLt,fb⟩
  have enough := n2.length_le_of_subset m2
  rw [← List.countP_eq_length_filter] at enough
  have sectors := sector_count hh S B
  change F.countP f = (dualRow G w).countP (faceSide S B) + 1 at sectors
  change ∃ b ∈ dualRow G w, faceSide S B b=true
  apply List.countP_pos_iff.mp
  simp only [List.length_cons,List.length_nil] at enough
  omega


private theorem selected_vertex {M} {G : IsDiskFullerene M h} {x y}
    (S : TriangleSide G (apex M) x y) {B f} (active : faceSide S B f=true)
    (v : Fin M.ord) (touch : v.val∈M.faces[f.val]) : vertexSide S B v=true := by
  classical
  obtain ⟨neq,fs⟩ := Bool.and_eq_true_iff.mp active
  have good : f≠apex M ∧ f≠x ∧ f≠y := of_decide_eq_true neq
  have c := S.color_at good touch
  have cf : S.color v.val ↔ S.part.left v :=
    ⟨fun ⟨_,k⟩ => k,fun k => ⟨v.isLt,k⟩⟩
  change (decide (S.faceColor f) == B)=true at fs
  simpa [vertexSide,← cf,← c] using fs

private theorem edge_data {M} (G : IsDiskFullerene M h) {x y : Face M} (adj : y∈dualRow G x) :
    ∃ e : Edge M, Across (dual G) e x y ∧ (primal G e).1.val ∈ M.faces[x.val] := by
  obtain ⟨dart,hx,hy⟩ := (mem_row_iff G x y).mp adj
  obtain ⟨e,orient⟩ := repr_dart G (incident_dart G hx)
  refine ⟨e,crossTable G orient (Or.inl ⟨hx,hy⟩),?_⟩
  change (endpoints e).1∈_
  rcases orient with eq|eq <;> rw [eq]
  · exact (sideEnds hx).1
  · exact (sideEnds hx).2

theorem EndPiece.nonempty {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) :
    ∃ u, sectorCore d.seam d.side u=true := by
  classical
  obtain ⟨b,bC,bB⟩ := d.open_vertex hh
  let S := d.seam
  let B := d.side
  let w := apex M
  let x := atSide G w d.i
  let y := atSide G w d.j
  have bn := of_decide_eq_true (Bool.and_eq_true_iff.mp bB).1
  change b≠w ∧ b≠x ∧ b≠y at bn
  obtain ⟨p,_,q,_,_,_,_,only⟩ := cycle_at (boundary_cycle G hh).1
    (by rw [(boundary_cycle G hh).2.1]; exact hh) bC
  apply Classical.byContradiction; intro empty
  have nb : dualRow G b ⊆ [w,p,q] := by
    intro v adj
    by_cases vw : v=w
    · simp [vw]
    by_cases vC : IsBoundary G v
    · obtain ⟨e,E,touch⟩ := edge_data G adj
      have cut := TerminalHalf.seam_or_cycle hh S B d.terminal bC vC E
        (.inl (selected_vertex S bB _ touch))
      rcases cut with edge|mark
      · have either := only v edge
        simp; grind
      · subst e
        have mid : Across (dual G) S.xy x y := S.middle
        rcases E with e|e <;> rcases mid with m|m <;> rw [e] at m <;> simp only [Prod.mk.injEq] at m <;> grind
    · have actual := (mem_diskInterior G v).mpr ⟨vw,vC⟩
      have xC : IsBoundary G x := by unfold IsBoundary x; rw [atSide_eq]; exact List.getElem_mem _
      have yC : IsBoundary G y := by unfold IsBoundary y; rw [atSide_eq]; exact List.getElem_mem _
      have vn : v≠w ∧ v≠x ∧ v≠y := ⟨vw,fun eq => vC (eq ▸ xC),fun eq => vC (eq ▸ yC)⟩
      have stable := S.edge_stays bn vn adj
      have fs : faceSide S B v=true := by
        simpa [faceSide,bn,vn,stable,S,B,w,x,y] using bB
      exact False.elim (empty ⟨v,Bool.and_eq_true_iff.mpr ⟨decide_eq_true actual,fs⟩⟩)
  have small := (row_nodup G (noRepeatOnSphere G hh) b).length_le_of_subset nb
  have degree := inner_degree G bn.1
  simp only [List.length_cons,List.length_nil] at small
  omega

theorem EndPiece.disjoint_core {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d e : EndPiece M G)
    (apart : ∀ v, ¬(vertexSide d.seam d.side v=true ∧ vertexSide e.seam e.side v=true)) :
    ∀ f, ¬(sectorCore d.seam d.side f=true ∧ sectorCore e.seam e.side f=true) := by
  rintro f ⟨left,right⟩
  obtain ⟨v,w,corner⟩ := face_dart G hh f
  let t : Fin M.ord := ⟨v,(dart_info G (incident_dart G corner)).1⟩
  exact apart t ⟨core_corner_selected d.seam left t (sideEnds corner).1,
    core_corner_selected e.seam right t (sideEnds corner).1⟩

end DiskFullerene.Dual
