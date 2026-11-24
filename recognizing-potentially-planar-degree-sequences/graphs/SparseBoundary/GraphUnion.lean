import SparseBoundary.GraphCliqueSum
import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary.Graph

private def unionRel (G : Graph n) (H : Graph m) : Fin (n+m) → Fin (n+m) → Bool :=
  Fin.addCases (fun u => Fin.addCases (G.adj u) (fun _ => false))
    (fun v => Fin.addCases (fun _ => false) (H.adj v))

def union (G : Graph n) (H : Graph m) : Graph (n+m) := ofRelation (unionRel G H)

private theorem union_adj (G : Graph n) (H : Graph m) (x y : Fin (n+m)) :
    (G.union H).adj x y=unionRel G H x y := by
  apply adj_ofRelation
  · intro u v
    refine Fin.addCases ?_ ?_ u <;> intro i <;> refine Fin.addCases ?_ ?_ v <;> intro j <;>
      simp [unionRel,G.adj_comm,H.adj_comm]
  · intro u
    refine Fin.addCases ?_ ?_ u <;> intro i <;> simp [unionRel]

private theorem all_one_side {G : Graph n} {R : Fin k → Fin k → Bool} {s} (start : Fin k)
    (paths : ∀ j, j=start ∨ R start j=true ∨ ∃ t,R start t=true ∧ R t j=true)
    (model : G.minorTest R s=true) (P : Fin n → Prop)
    (invariant : ∀ x y, G.adj x y=true → (P x ↔ P y)) :
    (∀ i,∀ x∈s i,P x) ∨ (∀ i,∀ x∈s i,¬P x) := by
  classical
  obtain ⟨hc,_,hl⟩ := bag_data model
  have nonempty (i) : ∃ z,z∈s i := by
    cases hs : s i with
    | nil => have hh := hc i; simp [hs,connected] at hh
    | cons u us => exact ⟨u,by simp⟩
  let rep i := Classical.choose (nonempty i)
  have mem i := Classical.choose_spec (nonempty i)
  have within (i) (x) (hx : x∈s i) : P x ↔ P (rep i) :=
    uniform_bag (hc i) P (fun x _ y _ => invariant x y) x hx _ (mem i)
  have onEdge (i j) (e : R i j=true) : P (rep i) ↔ P (rep j) := by
    obtain ⟨x,hx,y,hy,xy⟩ := hl i j e
    exact (within i x hx).symm.trans ((invariant x y xy).trans (within j y hy))
  have all (i) (x) (hx : x∈s i) : P (rep start) ↔ P x := by
    apply Iff.trans _ (within i x hx).symm
    rcases paths i with rfl|e|⟨j,hj,e⟩
    · rfl
    · exact onEdge start i e
    · exact (onEdge start j hj).trans (onEdge j i e)
  by_cases left : P (rep start)
  · exact Or.inl fun i x h => (all i x h).mp left
  · exact Or.inr fun i x h hx => left ((all i x h).mpr hx)

/-- The disjoint union has no forbidden connected minor if both components
    are planar. Explicit default vertices are only used for the projections. -/
theorem union_planar {G : Graph n} {H : Graph m} (pg : G.Planar) (ph : H.Planar)
    (u : Fin n) (v : Fin m) : (G.union H).Planar := by
  let left (x : Fin (n+m)) := x.val<n
  have invariant (x y) (h : (G.union H).adj x y=true) : left x ↔ left y := by
    refine Fin.addCases ?_ ?_ x h <;> intro i <;> refine Fin.addCases ?_ ?_ y <;> intro j <;>
      simp [union_adj,unionRel,left] <;> omega
  have pull {k : Nat} {R : Fin k → Fin k → Bool} (ir : ∀ i,R i i=false) (start : Fin k)
      (paths : ∀ j,j=start ∨ R start j=true ∨ ∃ t, R start t=true ∧ R t j=true)
      (s) (h : (G.union H).minorTest R s=true) :
      (∃ bags,G.minorTest R bags=true) ∨ (∃ bags,H.minorTest R bags=true) := by
    rcases all_one_side start paths h left invariant with l|r
    · left
      let f : Fin (n+m) → Fin n := Fin.addCases id (fun _ => u)
      have eq (x) (hx : left x) : (f x).castAdd m=x := by
        refine Fin.addCases ?_ ?_ x hx <;> intro i <;> simp [left,f] <;> omega
      apply transfer_minor ir s h f
      · intro x y
        refine Fin.addCases ?_ ?_ x <;> intro i <;> refine Fin.addCases ?_ ?_ y <;> intro j <;>
          simp [f,union_adj,unionRel] <;> exact Or.inr
      · intro i j hij x hx y hy same
        have e := congrArg (Fin.castAdd m) same
        rw [eq x (l i x hx),eq y (l j y hy)] at e
        exact (bag_data h).2.1 i j hij x hx (e ▸ hy)
    · right
      let f : Fin (n+m) → Fin m := Fin.addCases (fun _ => v) id
      have eq (x) (hx : ¬left x) : (f x).natAdd n=x := by
        refine Fin.addCases ?_ ?_ x hx <;> intro i <;> simp [left,f] <;> omega
      apply transfer_minor ir s h f
      · intro x y
        refine Fin.addCases ?_ ?_ x <;> intro i <;> refine Fin.addCases ?_ ?_ y <;> intro j <;>
          simp [f,union_adj,unionRel] <;> exact Or.inr
      · intro i j hij x hx y hy same
        have e := congrArg (Fin.natAdd n) same
        rw [eq x (r i x hx),eq y (r j y hy)] at e
        exact (bag_data h).2.1 i j hij x hx (e ▸ hy)
  exact ⟨fun ⟨s,h⟩ => (pull (by decide) 0 (by decide) s h).elim pg.1 ph.1,
    fun ⟨s,h⟩ => (pull (by decide) 0 (by decide) s h).elim pg.2 ph.2⟩

theorem union_range (n m : Nat) : List.finRange (n+m) =
    (List.finRange n).map (Fin.castAdd m) ++ (List.finRange m).map (Fin.natAdd n) := by
  apply List.ext_getElem
  · simp
  · intro i h _
    by_cases hi : i<n
    · rw [List.getElem_append_left (by simpa using hi : i<((List.finRange n).map (Fin.castAdd m)).length)]
      apply Fin.ext; simp
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi :
          ((List.finRange n).map (Fin.castAdd m)).length≤i)]
      apply Fin.ext; simp; omega

theorem union_degree_left (G : Graph n) (H : Graph m) (x : Fin n) :
    (G.union H).degree (x.castAdd m)=G.degree x := by
  unfold degree
  rw [union_range n m]
  simp [List.filter_append,List.filter_map,Function.comp_def,union_adj,unionRel]

theorem union_degree_right (G : Graph n) (H : Graph m) (x : Fin m) :
    (G.union H).degree (x.natAdd n)=H.degree x := by
  unfold degree
  rw [union_range n m]
  simp [List.filter_append,List.filter_map,Function.comp_def,union_adj,unionRel]

end SparseBoundary.Graph

namespace SparseBoundary

/-- Independent planar realizations may be combined by concatenating their
    degree profiles, even when a profile is empty. -/
theorem planaric_append {d e : List Nat} (hp : Planaric d) (hq : Planaric e) : Planaric (d++e) := by
  by_cases ld : d=[]
  · simpa [ld] using hq
  by_cases le : e=[]
  · simpa [le] using hp
  obtain ⟨G,rg,pg⟩ := hp
  obtain ⟨H,rh,ph⟩ := hq
  let u : Fin d.length := ⟨0,List.length_pos_iff.mpr ld⟩
  let v : Fin e.length := ⟨0,List.length_pos_iff.mpr le⟩
  have p := Graph.planaric_profile (Graph.union_planar pg ph u v)
  have row : List.ofFn (G.union H).degree=d++e := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp only [List.getElem_ofFn]
      by_cases l : i<d.length
      · rw [List.getElem_append_left l]
        exact (Graph.union_degree_left G H ⟨i,l⟩).trans (rg _)
      · rw [List.getElem_append_right (Nat.le_of_not_gt l)]
        let x : Fin e.length := ⟨i-d.length,by simp at hi; omega⟩
        have same : (x.natAdd d.length).val=i := by dsimp [x]; omega
        have eqf : (⟨i,by simpa using hi⟩ : Fin (d.length+e.length))=x.natAdd d.length := Fin.ext same.symm
        rw [eqf,Graph.union_degree_right]
        exact rh x
  rwa [row] at p

end SparseBoundary
