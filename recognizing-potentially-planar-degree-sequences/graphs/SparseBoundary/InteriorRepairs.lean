import SparseBoundary.InteriorNear
import SparseBoundary.UpperLists
import SparseBoundary.GraphUnion

namespace SparseBoundary

theorem graphic_degree_lt {d : List Nat} (hg : Graphic d) (a) (ha : a∈d) : a<d.length := by
  obtain ⟨G,real⟩ := hg
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem ha
  let v : Fin d.length := ⟨i,hi⟩
  have deg := (real v).trans eq
  have small := List.length_filter_le (G.adj v) (List.finRange d.length)
  have strict : ((List.finRange d.length).filter (G.adj v)).length ≠ (List.finRange d.length).length := by
    intro h
    have := List.length_filter_eq_length_iff.mp h v (List.mem_finRange v)
    simp at this
  simp only [List.length_finRange] at small strict
  unfold Graph.degree at deg
  omega

private def extra := List.replicate 4 3
private def endpoints : List (List Nat) :=
  [[4,4,4,4,4], [5,5,5,3,3,3], [5,4,4,4,4,3], [6,5,5,3,3,3,3], [4,4,4,4,4,4,4]]
private def repairs : List (Nat × Nat) :=
  [(6,56575943215),(7,29859016884847),(7,32058106733103),(8,33302111397102191),(8,14168427229897263)]

private theorem repair_pair {r : List Nat} (he : r∈endpoints) : Planaric (extra++r) := by
  have data : ∃ e∈repairs,
       let G : Graph (e.1+3) := ⟨BitVec.ofNat _ e.2⟩
       RimGrowth.Ordered G ∧ (List.ofFn G.degree).Perm (extra++r) := by
    simp [endpoints] at he
    rcases he with rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact ⟨(6,56575943215),by decide,by unfold RimGrowth.Ordered; decide +kernel,by decide +kernel⟩
      | exact ⟨(7,29859016884847),by decide,by unfold RimGrowth.Ordered; decide +kernel,by decide +kernel⟩
      | exact ⟨(7,32058106733103),by decide,by unfold RimGrowth.Ordered; decide +kernel,by decide +kernel⟩
      | exact ⟨(8,33302111397102191),by decide,by unfold RimGrowth.Ordered; decide +kernel,by decide +kernel⟩
      | exact ⟨(8,14168427229897263),by decide,by unfold RimGrowth.Ordered; decide +kernel,by decide +kernel⟩
  obtain ⟨e,_,h,perm⟩ := data
  exact (planaric_perm perm).mp (Graph.planaric_profile (RimGrowth.ordered_planar h))

/-- Every all-high upper exception is repaired by adjoining four threes.
    The graphs in the conclusion all have volume 4n-4. -/
theorem upper_exception_add_four_threes {r : List Nat} (core : Core r) (hg : Graphic r)
    (sum : r.sum=4*r.length) (bad : Exceptional r) :
    Planaric (List.replicate 4 3++r) := by
  have shape := (exceptional_profile (t:=0) (l:=0) core
    (by simp [profile] : r.Perm (profile r 0 0))).mp bad
  simp only [UpperForbidden,profile,List.replicate_zero,List.append_nil,Nat.add_zero] at shape
  apply repair_pair
  rcases shape with h5|⟨a,b,c,_,rfl⟩|rfl|rfl|rfl|rfl|rfl|rfl
  · have all4 (a) (ha : a∈r) : a≤4 := by have := graphic_degree_lt hg a ha; omega
    have eq : r=List.replicate 5 4 := by
      apply List.eq_replicate_iff.mpr
      refine ⟨h5,?_⟩
      have all (L : List Nat) (max : ∀ x∈L,x≤4) : L.sum≤4*L.length := by
        induction L with
        | nil => simp
        | cons x l ih =>
          have := max x (by simp)
          have := ih (fun y hy => max y (by simp [hy]))
          simp; omega
      intro x hx
      have perm := List.perm_cons_erase hx
      have sm := perm.sum_nat
      have len := perm.length_eq
      have remain := all (r.erase x) (fun y hy => all4 y (List.mem_of_mem_erase hy))
      have cap := all4 x hx
      simp only [List.sum_cons,List.length_cons] at sm len
      omega
    rw [eq]; decide
  · have max (x) (hx : x∈[a,b,c,3,3,3]) := graphic_degree_lt hg x hx
    have ha := max a (by simp)
    have hb := max b (by simp)
    have hc := max c (by simp)
    simp at ha hb hc sum
    have va : a=5 := by omega
    have vb : b=5 := by omega
    have vc : c=5 := by omega
    subst a; subst b; subst c; decide
  · decide
  · have := core.2 2 (by decide); omega
  · decide
  · have := core.2 2 (by decide); omega
  · decide
  · have := core.2 2 (by decide); omega

theorem cubic_clique : Planaric [3,3,3,3] := by
  let G : Graph 4 := ⟨63⟩
  exact ⟨G,by unfold Graph.Realizes; decide,RimGrowth.ordered_planar (G:=G) (by unfold RimGrowth.Ordered; decide)⟩

end SparseBoundary
