import SparseBoundary.LeafLift

namespace SparseBoundary.Graph

private def editRel (G : Graph n) (a b : Fin n) (value : Bool) (i j : Fin n) : Bool :=
  if (i=a ∧ j=b) ∨ (i=b ∧ j=a) then value else G.adj i j

/-- Change exactly one undirected edge. -/
def editEdge (G : Graph n) (a b : Fin n) (value : Bool) : Graph n :=
  ofRelation (editRel G a b value)

private theorem edit_adj {a b : Fin n} (h : a ≠ b) (G : Graph n) (v : Bool) (i j) :
    (G.editEdge a b v).adj i j = editRel G a b v i j := by
  apply adj_ofRelation
  · intro x y
    simp only [editRel]
    rw [G.adj_comm x y]
    grind
  · intro x
    simp only [editRel,adj_self]
    grind

private theorem degree_split (G : Graph n) (i w : Fin n) :
    G.degree i = (((List.finRange n).erase w).filter (G.adj i)).length +
      (if G.adj i w then 1 else 0) := by
  have h := ((List.perm_cons_erase (List.mem_finRange w)).filter (G.adj i)).length_eq
  cases e : G.adj i w <;> simpa [degree,List.filter_cons,e] using h

theorem degree_edit {a b : Fin n} (hne : a ≠ b) (G : Graph n) (v : Bool) (i) :
    (G.editEdge a b v).degree i +
      (if (i=a ∨ i=b) ∧ G.adj a b = true then 1 else 0) =
    G.degree i + (if (i=a ∨ i=b) ∧ v=true then 1 else 0) := by
  have endpoint {i w : Fin n} (e : (i=a ∧ w=b) ∨ (i=b ∧ w=a)) :
      (G.editEdge a b v).degree i + (if G.adj i w then 1 else 0) =
        G.degree i + (if v then 1 else 0) := by
    rw [degree_split G i w,degree_split (G.editEdge a b v) i w]
    have he : (G.editEdge a b v).adj i w = v := by
      rw [edit_adj hne]; simp [editRel,e]
    have hh : (((List.finRange n).erase w).filter ((G.editEdge a b v).adj i)) =
        (((List.finRange n).erase w).filter (G.adj i)) := by
      apply List.filter_congr
      intro j hj
      have hn : j ≠ w := fun h => (List.nodup_finRange n).not_mem_erase (h ▸ hj)
      rw [edit_adj hne]; simp only [editRel]; grind
    rw [he,hh]; omega
  by_cases ha : i=a
  · subst i; simpa using endpoint (i:=a) (w:=b) (Or.inl ⟨rfl,rfl⟩)
  by_cases hb : i=b
  · subst i; simpa [G.adj_comm b a] using endpoint (i:=b) (w:=a) (Or.inr ⟨rfl,rfl⟩)
  · have he : (G.editEdge a b v).adj i = G.adj i := by
      funext j; rw [edit_adj hne]; simp [editRel,ha,hb]
    simp [degree,he,ha,hb]

/-- If a vertex has strictly larger degree, one of its incident edges
    can be transferred to the lower-degree vertex without a multiple edge. -/
theorem transfer_edge {G : Graph n} {u v : Fin n} (gt : G.degree u < G.degree v) :
    ∃ H : Graph n, ∀ i, H.degree i + (if i=v then 1 else 0) =
      G.degree i + (if i=u then 1 else 0) := by
  have huv : u ≠ v := fun e => (Nat.lt_irrefl _) (e ▸ gt)
  let K := G.editEdge u v false
  have gap : K.degree u < K.degree v := by
    have a := degree_edit huv G false u
    have b := degree_edit huv G false v
    simp [K] at a b ⊢
    omega
  have exists_w : ∃ w, K.adj v w = true ∧ K.adj u w = false := by
    apply Classical.byContradiction
    intro hh
    apply (Nat.not_le_of_gt gap)
    apply List.Nodup.length_le_of_subset ((List.nodup_finRange n).filter _)
    intro i hi
    have e := (List.mem_filter.mp hi).2
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange _,?_⟩
    cases h : K.adj u i <;> grind
  obtain ⟨w,hv,hu⟩ := exists_w
  have hwu : w ≠ u := by
    intro e; subst w; simp [K,edit_adj huv,editRel] at hv
  have hwv : w ≠ v := by intro e; subst w; simp at hv
  have hv' : G.adj v w = true := by simpa [K,edit_adj huv,editRel,hwu,hwv,huv,Ne.symm huv] using hv
  have hu' : G.adj u w = false := by simpa [K,edit_adj huv,editRel,hwu,hwv,huv,Ne.symm huv] using hu
  let J := G.editEdge v w false
  have new_free : J.adj u w = false := by simp [J,edit_adj (Ne.symm hwv),editRel,Ne.symm hwu,huv,hu']
  refine ⟨J.editEdge u w true, fun i => ?_⟩
  have h1 := degree_edit (Ne.symm hwv) G false i
  have h2 := degree_edit (Ne.symm hwu) J true i
  change J.degree i + _ = _ at h1
  rw [hv'] at h1
  rw [new_free] at h2
  by_cases ea : i=u <;> by_cases eb : i=v <;> by_cases ec : i=w <;>
    simp_all <;> omega

private theorem degree_delete_zero (G : Graph (n+1)) (i : Fin n) :
    G.degree i.succ = (G.restrict Fin.succ).degree i +
      (if G.adj 0 i.succ then 1 else 0) := by
  have he : (G.restrict Fin.succ).adj i = G.adj i.succ ∘ Fin.succ :=
    funext (restrict_adj _ _ _)
  unfold degree
  rw [List.finRange_succ]
  simp only [List.filter_cons,List.filter_map,he, G.adj_comm i.succ 0]
  cases G.adj 0 i.succ <;> simp

/-- Lay off a leaf at an arbitrary maximum. The new graph realizes the
    original degrees with that maximum lowered by one. -/
theorem lay_off_leaf (G : Graph (n+1)) (leaf : G.degree 0 = 1) (v : Fin n)
    (maximum : ∀ i : Fin n, G.degree i.succ ≤ G.degree v.succ) :
    ∃ H : Graph n, ∀ i, H.degree i + (if i=v then 1 else 0) = G.degree i.succ := by
  have hrow : (((List.finRange n).filter (G.adj 0 ∘ Fin.succ))).length = 1 := by
    simpa [degree,List.finRange_succ,List.filter_map] using leaf
  obtain ⟨u,hu⟩ := List.length_eq_one_iff.mp hrow
  have hneigh (i : Fin n) : G.adj 0 i.succ = true ↔ i=u := by
    have h : i ∈ (List.finRange n).filter (G.adj 0 ∘ Fin.succ) ↔ i=u := by simp [hu]
    simpa [Function.comp_def] using h
  let K := G.restrict Fin.succ
  have degrees (i) : G.degree (Fin.succ i) = K.degree i + (if i=u then 1 else 0) := by
    simpa [hneigh] using degree_delete_zero G i
  by_cases eq : u=v
  · exact ⟨K, fun i => eq ▸ (degrees i).symm⟩
  have gap : K.degree u < K.degree v := by
    have du := degrees u
    have dv := degrees v
    have hm := maximum u
    simp [Ne.symm eq] at du dv
    omega
  obtain ⟨H,hH⟩ := transfer_edge gap
  exact ⟨H,fun i => (hH i).trans (degrees i).symm⟩

end SparseBoundary.Graph

namespace SparseBoundary

/-- Leaf deletion and reattachment at the level of graphical and planaric
    degree lists, in an ordering with the designated leaf first. -/
theorem leaf_reduction {d : List Nat} (v : Fin d.length) (orig : Graphic (1::d))
    (maximum : ∀ i : Fin d.length, d[i] ≤ d[v]) (positive : 1 ≤ d[v]) :
    let r := List.ofFn (fun i : Fin d.length => d[i] - (if i=v then 1 else 0))
    Graphic r ∧ (Planaric r → Planaric (1::d)) := by
  let f := fun i : Fin d.length => d[i] - (if i=v then 1 else 0)
  let r := List.ofFn f
  change Graphic r ∧ (Planaric r → Planaric (1::d))
  obtain ⟨G,hd⟩ := orig
  have hmax (i : Fin d.length) : G.degree i.succ ≤ G.degree v.succ := by
    rw [hd,hd]; exact maximum i
  obtain ⟨H,hH⟩ := Graph.lay_off_leaf G (hd 0) v hmax
  have hr : r.length = d.length := by simp [r]
  have indexed {a : List Nat} {k : Nat} (len : a.length=k) (K : Graph k)
      (hK : ∀ i, K.degree i = a[i.val]'(by omega)) : Graphic a := by
    subst k; exact ⟨K,hK⟩
  constructor
  · apply indexed hr H
    intro i
    have e := hH i
    rw [hd] at e
    change H.degree i + (if i=v then 1 else 0) = d[i.val] at e
    simp [r,f]
    exact Nat.eq_sub_of_add_eq e
  · intro hp
    let j : Fin r.length := ⟨v.val,by omega⟩
    have lift := planaric_attach_leaf hp j
    suffices he : (List.ofFn (fun i : Fin r.length => r[i] + (if i=j then 1 else 0))) = d by
      rwa [he] at lift
    apply List.ext_getElem
    · simp [hr]
    · intro i hi hi'
      by_cases eq : i=v.val
      · subst i; simp [r,f,j,Fin.ext_iff]
        change 1 ≤ d[v.val] at positive
        omega
      · simp [r,f,j,Fin.ext_iff,eq]

end SparseBoundary
