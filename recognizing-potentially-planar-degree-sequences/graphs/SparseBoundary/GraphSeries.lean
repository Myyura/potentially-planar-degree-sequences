import SparseBoundary.GraphSubdivision
import SparseBoundary.GraphEnumeration

namespace SparseBoundary.Graph

def pairRow (a b x : Fin n) : Bool := x == a || x == b

theorem row_two (a b : Fin n) (h : a ≠ b) :
    ((List.finRange n).filter (pairRow a b)).length = 2 := by
  have nod : ((List.finRange n).filter (pairRow a b)).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange _)
  have p : ((List.finRange n).filter (pairRow a b)).Perm [a,b] := by
    apply (List.perm_ext_iff_of_nodup nod (by simp [h])).mpr
    intro x
    simp [pairRow,List.mem_finRange]
  exact p.length_eq

/-- Add a two-edge path parallel to an existing edge. -/
def parallelPath (H : Graph n) (a b : Fin n) : Graph (n+1) := adjoinRow (pairRow a b) H

theorem parallelPath_planar {H : Graph n} (hp : H.Planar) {a b : Fin n}
    (he : H.adj a b = true) : (H.parallelPath a b).Planar := by
  apply degree_two_extension hp a b he
  · intro x y; simp [parallelPath,incident]
  · apply Fin.cases
    · simp
    · intro y; simp [parallelPath,incident,pairRow]

theorem parallelPath_new_degree {H : Graph n} {a b : Fin n} (he : H.adj a b = true) :
    (parallelPath H a b).degree 0 = 2 := by
  rw [parallelPath,degree_adjoin_zero]
  exact row_two a b (fun e => by subst b; simp at he)

theorem parallelPath_old_degree (H : Graph n) (a b x : Fin n) :
    (parallelPath H a b).degree x.succ = H.degree x + (pairRow a b x).toNat :=
  degree_adjoin_succ .. 

def eraseRel (H : Graph n) (a b x y : Fin n) : Bool :=
  H.adj x y && !((x == a && y == b) || (x == b && y == a))

def eraseEdge (H : Graph n) (a b : Fin n) : Graph n := ofRelation (eraseRel H a b)

theorem erase_adj (H : Graph n) (a b x y : Fin n) :
    (H.eraseEdge a b).adj x y = eraseRel H a b x y := by
  apply adj_ofRelation
  · intro i j
    rw [eraseRel,eraseRel,H.adj_comm]
    grind
  · simp [eraseRel]

theorem erase_source (H : Graph n) (a b : Fin n) (he : H.adj a b = true) :
    (H.eraseEdge a b).degree a + 1 = H.degree a := by
  have hne : a ≠ b := fun e => by subst b; simp at he
  let nbr := (List.finRange n).filter (H.adj a)
  have nb : b ∈ nbr := by simp [nbr,he,List.mem_finRange]
  have nd : nbr.Nodup := List.Pairwise.filter _ (List.nodup_finRange _)
  have hh : (H.eraseEdge a b).adj a = fun y => (y != b && H.adj a y) := by
    funext y; simp [erase_adj,eraseRel,beq_eq_false_iff_ne.mpr hne,Bool.and_comm,bne]
  have hl := List.length_erase_of_mem nb
  rw [nd.erase_eq_filter] at hl
  simp only [nbr,List.filter_filter] at hl
  simp only [degree,hh]
  have hpos := List.length_pos_of_mem nb
  dsimp [nbr] at hpos
  omega

private theorem erase_symm (H : Graph n) (a b : Fin n) : H.eraseEdge a b = H.eraseEdge b a := by
  apply eq_of_adj
  intro i j
  simp only [erase_adj,eraseRel,Bool.or_comm]

/-- Subdivide an edge, deleting its original copy. -/
def subdivide (H : Graph n) (a b : Fin n) : Graph (n+1) :=
  adjoinRow (pairRow a b) (H.eraseEdge a b)

theorem subdivide_planar {H : Graph n} (hp : H.Planar) {a b : Fin n} (he : H.adj a b = true) :
    (H.subdivide a b).Planar := by
  apply degree_two_extension hp a b he
  · intro x y
    simp only [subdivide,adjoin_adj,incident,Fin.cases_succ,erase_adj,eraseRel,Bool.and_eq_true]
    exact And.left
  · apply Fin.cases
    · simp
    · intro y; simp [subdivide,incident,pairRow]

theorem subdivide_new_degree {H : Graph n} {a b : Fin n} (he : H.adj a b = true) :
    (H.subdivide a b).degree 0 = 2 := by
  rw [subdivide,degree_adjoin_zero]
  exact row_two a b (fun e => by subst b; simp at he)

theorem subdivide_old_degree {H : Graph n} {a b : Fin n} (he : H.adj a b = true) (x : Fin n) :
    (H.subdivide a b).degree x.succ = H.degree x := by
  rw [subdivide,degree_adjoin_succ]
  by_cases ha : x=a
  · subst x; simpa [pairRow] using erase_source H a b he
  by_cases hb : x=b
  · subst x; rw [erase_symm]; simpa [pairRow] using erase_source H b a ((H.adj_comm _ _).trans he)
  have hh : (H.eraseEdge a b).adj x = H.adj x := by
    funext y; simp [erase_adj,eraseRel,ha,hb]
  simp [degree,hh,pairRow,ha,hb]

end SparseBoundary.Graph

namespace SparseBoundary

theorem planaric_add_two {d : List Nat} (hp : Planaric d) (h : ∃ x ∈ d, 0 < x) :
    Planaric (2::d) := by
  obtain ⟨G,hd,hp⟩ := hp
  obtain ⟨x,hx,hpos⟩ := h
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  let a : Fin d.length := ⟨i,hi⟩
  have ha : 0 < G.degree a := by rw [hd a]; exact he ▸ hpos
  obtain ⟨b,hb⟩ := List.length_pos_iff_exists_mem.mp ha
  have hab := (List.mem_filter.mp hb).2
  refine ⟨G.subdivide a b,?_,Graph.subdivide_planar hp hab⟩
  exact Fin.cases (Graph.subdivide_new_degree hab)
    (fun j => (Graph.subdivide_old_degree hab j).trans (hd j))

theorem planaric_add_twos {d : List Nat} (hp : Planaric d) (h : ∃ x ∈ d, 0 < x) (k : Nat) :
    Planaric (List.replicate k 2 ++ d) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    apply planaric_add_two ih
    obtain ⟨x,hx,hp'⟩ := h
    exact ⟨x,List.mem_append_right _ hx,hp'⟩

end SparseBoundary
