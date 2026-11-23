import DiskFullerene.FanMarks

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

private def unroll (n p a : Nat) := if p≤a then a-p else n+a-p

/-- Cutting a simple cycle at an unused vertex puts every edge amongst
the specified vertices between consecutive places of a linear order. -/
private theorem rankOn {α : Type} [DecidableEq α] (c small : List α) (nd : c.Nodup) (less : small.length<c.length) :
    ∃ rank : α→Nat, (∀ a∈c, ∀ b∈c, rank a=rank b → a=b) ∧
      ∀ a∈small, ∀ b∈small, OnCycle c a b → rank a+1=rank b ∨ rank b+1=rank a := by
  have ex : ∃ z∈c,z∉small := by apply Classical.byContradiction; intro lack; have cap := nd.length_le_of_subset (l₂:=small) (by intro x hx; exact Classical.byContradiction (fun nx=>lack ⟨x,hx,nx⟩)); omega
  obtain ⟨z,zc,zs⟩ := ex
  let p := c.idxOf z; have pb : p<c.length := List.idxOf_lt_length_iff.mpr zc
  let rank (a : α) := unroll c.length p (c.idxOf a)
  have inj {a b : α} (ac : a∈c) (bc : b∈c) (eq : c.idxOf a=c.idxOf b) : a=b := by
    have ha := List.idxOf_lt_length_iff.mpr ac; have hb := List.idxOf_lt_length_iff.mpr bc
    calc a = c[c.idxOf a] := (List.getElem_idxOf ha).symm
         _ = c[c.idxOf b] := by simp [eq]
         _ = b := List.getElem_idxOf hb
  refine ⟨rank,?_,?_⟩
  · intro a ac b bc equ; have ha := List.idxOf_lt_length_iff.mpr ac; have hb := List.idxOf_lt_length_iff.mpr bc
    apply inj ac bc; unfold rank unroll at equ; split at equ <;> split at equ <;> omega
  · intro a as b bs edge
    have oriented {a b : α} (bs : b∈small) (e : (a,b)∈sides c) : rank a+1=rank b := by
      obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp e; rw [sides_size] at hi; rw [side_at _ _ hi] at eq
      cases eq
      have hb : next c.length i≠p := by
        intro np; have q : c[next c.length i]'(next_bound hi)=z := by simp [np,p,List.getElem_idxOf pb]
        exact zs (q ▸ bs)
      unfold rank unroll; simp only [List.Nodup.idxOf_getElem nd]; unfold next at *; split at hb <;> simp_all <;> split <;> split <;> omega
    rcases edge with e|e; exact .inl (oriented bs e); exact .inr (oriented as e)

namespace TerminalAnnulus
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

abbrev junction (T : TerminalAnnulus d) (i : I) := (T.fans.arc i).first

theorem junction_boundary (T : TerminalAnnulus d) (i : I) : IsBoundary G (T.junction i) :=
  T.boundary (i:=i) (by simp [junction,Arc.word])

private theorem edge_kind (T : TerminalAnnulus d) (hh : 3≤h) {i : I} {a b : Face M}
    (ah : IsBoundary G a) (bh : IsBoundary G b) (edge : (a,b)∈sides (dualRow G (T.W.rim i))) :
    OnCycle (dualRow G (apex M)) a b ∨ Across (fun _ : Unit => (atSide G (apex M) d.i,atSide G (apex M) d.j)) () a b := by
  obtain ⟨e,v,cut,ends,mem,_⟩ := cornerEdge G edge
  have selected := core_corner_selected d.seam (T.rim_in i) v mem
  have side : vertexSide d.seam d.side (primal G e).1=true ∨ vertexSide d.seam d.side (primal G e).2=true := by rcases ends with h|h; exact .inl (h ▸ selected); exact .inr (h ▸ selected)
  rcases d.terminal.seam_or_cycle hh d.seam d.side ah bh cut side with outer|he
  · exact .inl outer
  · right; subst e; rcases d.seam.middle with eq|eq <;> rcases cut with h|h <;> simp [Across] <;> have fact := Prod.mk.inj (eq.symm.trans h) <;> grind

private theorem empty_edge (T : TerminalAnnulus d) (hh : 3≤h) {i : I} (e : (T.fans.arc i).mid=none) :
    OnCycle (dualRow G (apex M)) (T.junction i) (T.junction (after i)) ∨
      Across (fun _ : Unit => (atSide G (apex M) d.i,atSide G (apex M) d.j)) () (T.junction i) (T.junction (after i)) := by
  apply T.edge_kind hh (i:=i) (T.junction_boundary i) (T.junction_boundary (after i))
  change ((T.fans.arc i).first,(T.fans.arc (after i)).first)∈_
  rw [←T.fans.joined hh i]; apply (T.fans.corners i).mem_iff.mp; simp [Arc.word,e,sides]

private theorem neighbors_used {α} [DecidableEq α] {s r : List α} (nd : s.Nodup) (_rd : r.Nodup)
    (n : s.length=r.length) (sub : s⊆r) {v : α} (m : v∈r) : v∈s := by
  apply Classical.byContradiction; intro miss
  have msize := (List.nodup_cons.mpr ⟨miss,nd⟩).length_le_of_subset (List.cons_subset.mpr ⟨m,sub⟩)
  simp at msize; omega

private theorem marked_neighbors (T : TerminalAnnulus d) (hh : 3≤h) (i : I) {y} (yb : IsBoundary G y)
    (yAdj : y∈dualRow G (T.junction i)) (proper : ¬ OnCycle (dualRow G (apex M)) (T.junction i) y)
    {z} (zAdj : z∈dualRow G (T.junction i)) (pole : z≠apex M) (other : z≠y) :
    z=T.W.rim i ∨ z=T.W.rim (before i) ∨ OnCycle (dualRow G (apex M)) (T.junction i) z := by
  let x := T.junction i
  obtain ⟨p,q,nd,sub,clean,pc,qc⟩ := T.mark_slots hh (T.junction_boundary i) yb yAdj proper
  have safe (j : I) : T.W.rim j∉[apex M,p,q,y] := by
    intro mem; have fact := (mem_diskInterior G _).mp (core_disk (T.rim_in j)); exact (clean _ mem).elim fact.1 fact.2
  have neq : T.W.rim i≠T.W.rim (before i) := fun e=>(by decide : ∀ i : I, i≠before i) i (T.W.rim_injective _ _ e)
  let base : List (Face M) := [T.W.rim i,T.W.rim (before i)]++[apex M,p,q,y]
  have dn : base.Nodup := by apply List.nodup_append.mpr; refine ⟨by simp [neq],nd,?_⟩; intro a ha b hb ab; rcases List.mem_cons.mp ha with rfl|ha; exact safe i (ab ▸ hb); have eq := List.mem_singleton.mp ha; exact safe (before i) ((eq.symm.trans ab) ▸ hb)
  have row : base⊆dualRow G x := by
    apply List.append_subset.mpr; refine ⟨?_,sub⟩
    have a : i∈T.touches x := T.meets (by simp [x,junction,Arc.word]); have b := T.previous_meets hh i
    intro w m; simp at m; rcases m with rfl|rfl
    · exact (dual_adj_symmetric G _ _).mp (of_decide_eq_true (List.mem_filter.mp a).2)
    · exact (dual_adj_symmetric G _ _).mp (of_decide_eq_true (List.mem_filter.mp b).2)
  have low := dn.length_le_of_subset row
  have deg := inner_degree G (show x≠apex M from fun eq=>row_no_loop G hh _ (eq ▸ (show IsBoundary G x from T.junction_boundary i)))
  have l : base.length=6 := rfl
  have m := neighbors_used dn (row_nodup G (noRepeatOnSphere G hh) x) (by omega) row zAdj
  simp [base] at m; grind

private theorem other_arc_neighbor (T : TerminalAnnulus d) (hh : 3≤h) (i : I)
    (yAdj : T.junction (after i) ∈dualRow G (T.junction i))
    (proper : ¬OnCycle (dualRow G (apex M)) (T.junction i) (T.junction (after i))) :
    ∃ v, OnCycle (dualRow G (apex M)) (T.junction i) v ∧ OnCycle (dualRow G (apex M)) (T.junction (after i)) v := by
  let x := T.junction i; let y := T.junction (after i)
  have xb := T.junction_boundary i; have yb := T.junction_boundary (after i)
  have deg := inner_degree G (show x≠apex M from fun eq=>row_no_loop G hh _ (eq ▸ (show IsBoundary G x from xb)))
  obtain ⟨p,pm,q,qm,pq,py,yq,_⟩ := cycle_at (row_nodup G (noRepeatOnSphere G hh) x) (by omega) yAdj
  have pick : ∃ z, z≠T.W.rim i ∧ z∈dualRow G x ∧ OnCycle (dualRow G x) z y := by
    by_cases ep : p=T.W.rim i
    · exact ⟨q,fun e=>pq (ep.trans e.symm),qm,Or.inr yq⟩
    · exact ⟨p,ep,pm,Or.inl py⟩
  obtain ⟨z,notR,zx,side⟩ := pick
  have zy : z∈dualRow G y := by rcases side with e|e; exact (dual_adj_symmetric G _ _).mp (cyclic_link G _ e); exact cyclic_link G _ e
  have zy' : z≠y := fun eq=>row_no_loop G hh _ (eq ▸ zy)
  have zx' : z≠x := fun eq=>row_no_loop G hh _ (eq ▸ zx)
  have nz : z≠apex M := by
    intro eq; subst z
    rcases side with e|e; exact proper (Or.inr (turn_triangle G e).1); exact proper (Or.inl (turn_triangle G e).2)
  have cx := T.marked_neighbors hh i yb yAdj proper zx nz zy'
  have cy := T.marked_neighbors hh (after i) xb ((dual_adj_symmetric G _ _).mp yAdj) (fun c=>proper c.symm) zy nz zx'
  have ri : before (after i)=i := (by decide : ∀ k : I, before (after k)=k) i
  rw [ri] at cy
  have nd : T.W.rim (before i)≠T.W.rim (after i) := fun e=>(by decide : ∀ k : I, before k≠after k) i (T.W.rim_injective _ _ e)
  have out {j : I} {a : Face M} (o : OnCycle (dualRow G (apex M)) a z) : z≠T.W.rim j := by
    have on : IsBoundary G z := by
      rcases o with e|e <;> obtain ⟨n,hn,eq⟩ := List.mem_iff_getElem.mp e <;> rw [sides_size] at hn <;> rw [side_at _ _ hn] at eq
      · exact (Prod.mk.inj eq).2 ▸ List.getElem_mem _
      · exact (Prod.mk.inj eq).1 ▸ List.getElem_mem _
    exact fun eq=>(mem_diskInterior G _).mp (core_disk (T.rim_in j)) |>.2 (eq ▸ on)
  refine ⟨z,?_,?_⟩
  · rcases cx with r|r|e; exact False.elim (notR r); rcases cy with t|t|e; exact False.elim (nd (r.symm.trans t)); exact False.elim (notR t); exact False.elim (out e r); exact e
  · rcases cy with r|r|e; rcases cx with t|t|e; exact False.elim (notR t); exact False.elim (nd (t.symm.trans r)); exact False.elim (out e r); exact False.elim (notR r); exact e

private theorem pentacle {p : I→Nat} (inject : ∀ a b,p a=p b → a=b)
    (near : ∀ i, p i+1=p (after i) ∨ p (after i)+1=p i ∨ p i+2=p (after i) ∨ p (after i)+2=p i)
    (short : ∀ i j, i≠j → (p i+1=p (after i) ∨ p (after i)+1=p i) ∨ (p j+1=p (after j) ∨ p (after j)+1=p j)) : False := by
  let step (i : I) := p i+1=p (after i) ∨ p (after i)+1=p i
  have pinned : ∃ i, ∀ j, j≠i → step j := by
    by_cases all : ∀ j, step j
    · exact ⟨0,fun j _=>all j⟩
    · obtain ⟨i,off⟩ := Classical.not_forall.mp all
      exact ⟨i,fun j ne=>(short i j ne.symm).resolve_left off⟩
  obtain ⟨i,unit⟩ := pinned
  let a := after i; let b := after a; let c := after b; let d := after c
  have table : ∀ i : I, let a:=after i; let b:=after a; let c:=after b; let d:=after c;
    after d=i ∧ a≠i ∧ b≠i ∧ c≠i ∧ d≠i ∧ a≠c ∧ b≠d := by decide
  have ⟨last,ai,bi,ci,di,ac,bd⟩ := table i
  have a1 := unit a ai; have b1 := unit b bi; have c1 := unit c ci; have d1 := unit d di
  change p a+1=p b ∨ p b+1=p a at a1
  change p b+1=p c ∨ p c+1=p b at b1
  change p c+1=p d ∨ p d+1=p c at c1
  change p d+1=p (after d) ∨ p (after d)+1=p d at d1
  change after d=i at last; rw [last] at d1
  have e : p i+1=p a ∨ p a+1=p i ∨ p i+2=p a ∨ p a+2=p i := near i
  have nac : p a≠p c := fun eq=>ac (inject a c eq)
  have nbd : p b≠p d := fun eq=>bd (inject b d eq)
  have nci : p c≠p i := fun eq=>ci (inject c i eq)
  omega

/-- A pentagonal ring would put its five junctions on the boundary cycle
with four unit arcs and one arc of length at most two. Cutting that cycle
at an unused vertex rules out the resulting closed walk on a line. -/
theorem has_subdivision (T : TerminalAnnulus d) (hh : 7≤h) : ∃ i z, (T.fans.arc i).mid=some z := by
  have h3 : 3≤h := by omega
  apply Classical.byContradiction; intro absent
  let C := dualRow G (apex M)
  let F := T.junction
  let cyc (i : I) := OnCycle C (F i) (F (after i))
  have empty (i : I) : (T.fans.arc i).mid=none := by cases he : (T.fans.arc i).mid with | none => rfl | some z => exact False.elim (absent ⟨_,_,he⟩)
  have edge (i : I) := T.empty_edge h3 (empty i)
  have inject (i j : I) : F i=F j → i=j := T.distinct_corners h3 i j
  have rare {i j : I} (ni : ¬cyc i) (nj : ¬cyc j) : i=j := by
    have a := (edge i).resolve_left ni; have b := (edge j).resolve_left nj
    have perm : (F i=F j ∧ F (after i)=F (after j)) ∨ (F i=F (after j) ∧ F (after i)=F j) := by
      rcases a with e|e <;> rcases b with f|f <;> have comp := Prod.mk.inj (e.symm.trans f) <;> grind
    rcases perm with ⟨p,_⟩|⟨q,f⟩
    · exact inject _ _ p
    · have e := inject _ _ q; have f' := inject _ _ f
      have table : ∀ i : I, after (after i)≠i := by decide
      exact False.elim (table i (by rw [f',←e]))
  have bridge : ∃ v, ∀ i, ¬cyc i → OnCycle C (F i) v ∧ OnCycle C (F (after i)) v := by
    by_cases yes : ∃ i, ¬cyc i
    · obtain ⟨i,ni⟩ := yes
      have E : F (after i)∈dualRow G (F i) := by
        apply cyclic_link G (T.W.rim i)
        change ((T.fans.arc i).first, (T.fans.arc (after i)).first)∈_
        rw [←T.fans.joined h3 i]; apply (T.fans.corners i).mem_iff.mp; simp [Arc.word,empty i,sides]
      obtain ⟨v,vx,vy⟩ := T.other_arc_neighbor h3 i E ni
      exact ⟨v,fun j nj=>rare nj ni ▸ ⟨vx,vy⟩⟩
    · exact ⟨apex M,fun i m=>False.elim (yes ⟨i,m⟩)⟩
  obtain ⟨v,link⟩ := bridge
  let chosen := v::(List.finRange 5).map F
  have cb := boundary_cycle G h3
  have rank := rankOn C chosen cb.1 (by change ((v::(List.finRange 5).map F).length)<(dualRow G (apex M)).length; simp [cb.2.1]; omega)
  obtain ⟨p,pinj,pr⟩ := rank
  let n (i : I) := p (F i)
  have inc (i : I) : F i∈chosen := by simp [chosen]
  have vn : v∈chosen := by simp [chosen]
  have direct (i : I) (h : cyc i) : n i+1=n (after i) ∨ n (after i)+1=n i := pr _ (inc i) _ (inc _) h
  apply pentacle (p:=n) (fun a b eq=>inject a b (pinj _ (T.junction_boundary a) _ (T.junction_boundary b) eq))
  · intro i
    by_cases h : cyc i
    · rcases direct _ h with e|e; exact .inl e; exact .inr (.inl e)
    · have ⟨a,b⟩ := link i h; have ha := pr _ (inc i) v vn a; have hb := pr _ (inc (after i)) v vn b
      have different : n i≠n (after i) := fun eq=>(by decide : ∀ i : I, i≠after i) i (inject _ _ (pinj _ (T.junction_boundary i) _ (T.junction_boundary (after i)) eq))
      change n i+1=p v ∨ p v+1=n i at ha; change n (after i)+1=p v ∨ p v+1=n (after i) at hb
      omega
  · intro i j ne
    by_cases first : cyc i
    · exact .inl (direct i first)
    · exact .inr (direct j (Classical.byContradiction (fun nj=>ne (rare first nj))))

end TerminalAnnulus
end DiskFullerene.EndFans
