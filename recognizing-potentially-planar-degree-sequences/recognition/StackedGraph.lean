import SourceMap
import Promise

namespace Recognition.StackedGraph
open SourceMap Connectivity SparseBoundary SparseBoundary.Graph Promise

/-- The face and neighbour fields of a constructed mesh have the same vertex
set. The carrier is restricted because unused natural-number labels are legal. -/
private structure Good (M : Mesh) : Prop where
  corners : ∀ f, M.face f → M.vertex f.a ∧ M.vertex f.b ∧ M.vertex f.c ∧
    f.a ≠ f.b ∧ f.a ≠ f.c ∧ f.b ≠ f.c
  nodup : ∀ u, M.vertex u → (M.neighbors u).Nodup
  valid : ∀ u v, M.vertex u → v ∈ M.neighbors u → M.vertex v
  irreflexive : ∀ u, M.vertex u → u ∉ M.neighbors u
  symmetric : ∀ u v, M.vertex u → M.vertex v → (v ∈ M.neighbors u ↔ u ∈ M.neighbors v)

private theorem tetra_good : Good tetra := by
  constructor
  · intro f h
    change f.a<f.b ∧ f.b<f.c ∧ f.c<4 at h
    change f.a<4 ∧ f.b<4 ∧ f.c<4 ∧ _
    omega
  · intro u hu
    change u<4 at hu
    simp only [tetra,ite_eq_left hu]
    exact (List.nodup_range (n:=4)).filter _
  · intro u v hu h
    change u<4 at hu
    simp [tetra,hu] at h
    exact h.1
  · intro u hu
    change u<4 at hu
    simp [tetra,hu]
  · intro u v hu hv
    change u<4 at hu
    change v<4 at hv
    simp [tetra,hu,hv,ne_comm]

private theorem member_corner (f : Face) (v : Nat) : v ∈ [f.a,f.b,f.c] ↔ f.hit v := by
  simp [Face.hit]

private theorem good_insert (g : Good M) (face : M.face f) (fresh : ¬M.vertex x) :
    Good (stack M f x) := by
  obtain ⟨a,b,c,ab,ac,bc⟩ := g.corners f face
  have ax : f.a≠x := fun e => fresh (e ▸ a)
  have bx : f.b≠x := fun e => fresh (e ▸ b)
  have cx : f.c≠x := fun e => fresh (e ▸ c)
  have notIn (u : Nat) (hu : M.vertex u) : x ∉ M.neighbors u := fun h => fresh (g.valid u x hu h)
  have hhit (v : Nat) (h : f.hit v) : M.vertex v := by
    rcases h with rfl|rfl|rfl <;> assumption
  constructor
  · intro s hs
    rcases hs with ⟨hs,_⟩|rfl|rfl|rfl
    · obtain ⟨i,j,k,ij,ik,jk⟩ := g.corners s hs
      exact ⟨.inr i,.inr j,.inr k,ij,ik,jk⟩
    · exact ⟨.inr a,.inr b,.inl rfl,ab,ax,bx⟩
    · exact ⟨.inr a,.inr c,.inl rfl,ac,ax,cx⟩
    · exact ⟨.inr b,.inr c,.inl rfl,bc,bx,cx⟩
  · intro u hu
    rcases hu with rfl|old
    · simp [stack,ab,ac,bc]
    · have ux : u≠x := fun e => fresh (e ▸ old)
      by_cases h : f.hit u <;> simp [stack,ux,h,notIn u old,g.nodup u old]
  · intro u v hu hv
    rcases hu with rfl|old
    · have mem : f.hit v := (member_corner _ _).mp (by simpa [stack] using hv)
      exact .inr (hhit v mem)
    · have ux : u≠x := fun e => fresh (e ▸ old)
      by_cases h : f.hit u
      · have mem : v=x ∨ v∈M.neighbors u := by simpa [stack,ux,h] using hv
        exact mem.imp_right (g.valid u v old)
      · exact .inr (g.valid u v old (by simpa [stack,ux,h] using hv))
  · intro u hu
    rcases hu with rfl|old
    · simp [stack,Ne.symm ax,Ne.symm bx,Ne.symm cx]
    · have ux : u≠x := fun e => fresh (e ▸ old)
      by_cases h : f.hit u <;> simp [stack,ux,h,g.irreflexive u old]
  · intro u v hu hv
    by_cases ux : u=x
    · subst u
      by_cases vx : v=x
      · subst v; rfl
      · have vold := hv.resolve_left vx
        by_cases hit : f.hit v <;> simp [stack,vx,Face.hit] at hit ⊢ <;> grind
    · have uold := hu.resolve_left ux
      by_cases vx : v=x
      · subst v
        by_cases hit : f.hit u <;> simp [stack,ux,Face.hit] at hit ⊢ <;> grind
      · have vold := hv.resolve_left vx
        by_cases h : f.hit u <;> by_cases k : f.hit v <;>
          simp [stack,ux,vx,h,k,g.symmetric u v uold vold]

private theorem good (h : Stacked M) : Good M := by
  induction h with
  | tetra => exact tetra_good
  | insert _ f fresh ih => exact good_insert ih f fresh

private abbrev V (M : Mesh) := {v : Nat // M.vertex v}
private def E (M : Mesh) (u v : V M) : Prop := v.val ∈ M.neighbors u.val

private theorem robustMesh (s : Stacked M) : Robust (E M) := by
  classical
  induction s with
  | tetra =>
    intro gone _ u v hu hv
    by_cases eq : u=v
    · subst v; exact .stay hu
    · have ne : v.val ≠ u.val := fun e => eq (Subtype.ext e.symm)
      apply Survives.step (.stay hu) _ hv
      simp [E,tetra,show u.val<4 from u.property,show v.val<4 from v.property,ne]
  | @insert M f x s face fresh ih =>
    let old (v : V M) : V (stack M f x) := ⟨v.val,.inr v.property⟩
    let newV : V (stack M f x) := ⟨x,.inl rfl⟩
    let fwd : Sum (V M) Unit → V (stack M f x) := Sum.elim old (fun _ => newV)
    let back (v : V (stack M f x)) : Sum (V M) Unit :=
      if h : M.vertex v.val then .inl ⟨v.val,h⟩ else .inr ()
    obtain ⟨a,b,c,ab,ac,bc⟩ := (good s).corners _ face
    let choose (v : V M) : List Unit := if f.hit v.val then [()] else []
    have sym (i j : V M) : E M i j → E M j i := ((good s).symmetric _ _ i.property j.property).mp
    have r := robust_extension sym ih choose (fun j =>
      ⟨[⟨f.a,a⟩,⟨f.b,b⟩,⟨f.c,c⟩],by simp [Subtype.ext_iff,ab,ac,bc],rfl,by
        cases j
        intro v mem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
        rcases mem with rfl|rfl|rfl <;> simp [choose,Face.hit]⟩)
    apply robust_relabel fwd back _ _ _ r
    · intro v
      dsimp [back,fwd]
      split
      · rfl
      · rename_i h
        apply Subtype.ext
        exact (v.property.resolve_right h).symm
    · intro v
      cases v with
      | inl v => simp [fwd,back,old,v.property]
      | inr v => simp [fwd,back,newV,fresh]
    · intro u v edge
      cases u with
      | inl u =>
        have ux : u.val ≠ x := fun e => fresh (e ▸ u.property)
        cases v with
        | inl v =>
          change v.val ∈ (stack M f x).neighbors u.val
          change v.val ∈ M.neighbors u.val at edge
          by_cases h : f.hit u.val <;> simp [stack,ux,h,edge]
        | inr j =>
          change j ∈ choose u at edge
          change x ∈ (stack M f x).neighbors u.val
          by_cases h : f.hit u.val <;> simp_all [choose,stack]
      | inr j =>
        cases v with
        | inl v =>
          change j ∈ choose v at edge
          change v.val ∈ (stack M f x).neighbors x
          by_cases h : f.hit v.val
          · simpa [stack] using (member_corner f v.val).2 h
          · simp [choose,h] at edge
        | inr => exact edge.elim

/-- A constructed spherical mesh with these labels and degrees gives a
three-connected realization in the project's packed simple-graph model. -/
theorem from_stacked {xs : List Nat} (four : 4 ≤ xs.length) (h : Stacked M)
    (names : ∀ v, M.vertex v ↔ v < xs.length)
    (degrees : ∀ i : Fin xs.length, (M.neighbors i.val).length = xs[i]) :
    ThreeConnectedRow xs := by
  let rel (u v : Fin xs.length) := (M.neighbors u.val).contains v.val
  let g := ofRelation rel
  have vertex (i : Fin xs.length) := (names i.val).2 i.isLt
  have adj (i j : Fin xs.length) : g.adj i j = rel i j := by
    apply adj_ofRelation
    · intro u v
      simp [rel,(good h).symmetric _ _ (vertex u) (vertex v)]
    · intro u
      simp [rel,(good h).irreflexive _ (vertex u)]
  refine ⟨four,g,fun i => ?_,?_⟩
  · let ns := ((List.finRange xs.length).filter (g.adj i)).map Fin.val
    have hn : ns.Nodup := List.Pairwise.map _ (fun _ _ ne e => ne (Fin.ext e))
      ((List.nodup_finRange _).filter _)
    have p : ns.Perm (M.neighbors i.val) := by
      apply (List.perm_ext_iff_of_nodup hn ((good h).nodup _ (vertex i))).mpr
      intro v
      simp only [ns,List.mem_map,List.mem_filter,List.mem_finRange,true_and,adj,rel,List.contains_iff_mem]
      constructor
      · rintro ⟨z,hz,rfl⟩; exact hz
      · intro hz
        have bound := (names v).1 ((good h).valid _ _ (vertex i) hz)
        exact ⟨⟨v,bound⟩,hz,rfl⟩
    exact (by simpa [ns,Graph.degree] using p.length_eq : g.degree i = _).trans (degrees i)
  · let f (v : V M) : Fin xs.length := ⟨v.val,(names v.val).1 v.property⟩
    let u (i : Fin xs.length) : V M := ⟨i.val,vertex i⟩
    apply robust_relabel f u (fun _ => rfl) (fun _ => rfl) _ (robustMesh h)
    intro v w he
    simpa [adj,rel,f,E] using he

theorem encoded_three_connected (I : Recognition.Reduction.Instance) (hv : Recognition.Reduction.Valid I) :
    ThreeConnectedRow (Recognition.Reduction.encode I) := by
  obtain ⟨M,stacked,names,row⟩ := source_bare_stacked I hv
  have size := (Recognition.Reduction.source_valid I hv).1
  apply Promise.encoded_three_connected I hv
  exact from_stacked (by omega) stacked names row

private def fallback : Graph 6 :=
  ofRelation (fun i j => decide (i ≠ j ∧ (i.val < 3 ∨ j.val < 3)))

private theorem fallback_adj (i j : Fin 6) :
    fallback.adj i j = decide (i ≠ j ∧ (i.val < 3 ∨ j.val < 3)) := by
  apply adj_ofRelation
  · intro a b; simp only [decide_eq_decide]; grind
  · simp

private theorem malformed_connected : ThreeConnectedRow Reduction.malformedOutput := by
  refine ⟨by decide, fallback, by unfold Graph.Realizes Reduction.malformedOutput; decide +kernel, ?_⟩
  change Robust (fun x y : Fin 6 => fallback.adj x y = true)
  intro gone few a b ha hb
  have hub : ∃ i : Fin 6, i ∈ [0,1,2] ∧ i ∉ gone := by
    apply Classical.byContradiction
    intro no
    have sub : ([0,1,2] : List (Fin 6)) ⊆ gone :=
      fun i hm => Classical.byContradiction (fun miss => no ⟨i,hm,miss⟩)
    have size := (show ([0,1,2] : List (Fin 6)).Nodup by decide).length_le_of_subset sub
    simp only [List.length_cons,List.length_nil] at size
    omega
  obtain ⟨i,hi,ok⟩ := hub
  have hh : i.val < 3 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  have first : Survives (fun u v => fallback.adj u v = true) gone a i := by
    by_cases h : a=i
    · subst a; exact .stay ok
    · exact .step (.stay ha) (by simp [fallback_adj,h,hh]) ok
  by_cases e : i=b
  · subst b; exact first
  · exact .step first (by simp [fallback_adj,e,hh]) hb

/-- The total instance map, including invalid arithmetic input, always has
a labelled three-connected simple realization. -/
theorem reduction_three_connected (I : Reduction.Instance) :
    ThreeConnectedRow (Reduction.reduceInstance I) := by
  by_cases valid : Reduction.Valid I
  · rw [Reduction.reduce_valid _ valid]
    exact encoded_three_connected I valid
  · rw [Reduction.reduce_invalid _ valid]
    exact malformed_connected

end Recognition.StackedGraph
