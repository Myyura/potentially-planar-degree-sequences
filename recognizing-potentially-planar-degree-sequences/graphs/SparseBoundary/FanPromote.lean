import SparseBoundary.FanExpansion
import SparseBoundary.GraphDeletion
import SparseBoundary.GraphPerm

namespace SparseBoundary.Fan

open Graph

/-- Duplicate the edge from a hub to a degree-two neighbour. The old
neighbour becomes the new three, and the new subdivision vertex replaces
its old two in the degree multiset. -/
theorem promote_adjacent_two {a : Nat} {xs : List Nat} {G : Graph (a::xs).length}
    (hp : G.Planar) (hd : G.Realizes (a::xs)) (i : Fin xs.length)
    (hi : xs[i]=2) (edge : G.adj 0 i.succ=true) :
    Planaric (3::(a+1)::xs) := by
  let Y := xs.set i.val 3
  have hn : (2::(a+1)::Y).length=(a::xs).length+1 := by simp [Y]
  have init : Planaric (2::(a+1)::Y) := by
    apply (planaric_on_labels hn).mpr
    refine ⟨copyEdge G 0 i.succ,copy_planar hp edge,?_⟩
    refine Fin.cases (copy_new_degree edge) (fun j => ?_)
    refine Fin.cases ?_ (fun v => ?_) j
    · change (copyEdge G 0 i.succ).degree (Fin.succ 0)=a+1
      rw [copy_old_degree]
      have h : G.degree 0=a := hd 0
      simp [h,hit]
    · change (copyEdge G 0 i.succ).degree v.succ.succ=Y[v.val]'(by simp [Y])
      rw [copy_old_degree]
      have h : G.degree v.succ=xs[v] := hd v.succ
      by_cases eq : v=i
      · subst v
        simp [h,hi,hit,Y]
      · have ne : i.val≠v.val := fun e => eq (Fin.ext e.symm)
        simp [h,hit,Y,List.getElem_set_ne ne,eq,Fin.succ_ne_zero]
  have eqperm : (2::(a+1)::Y).Perm (3::(a+1)::xs) := by
    apply List.perm_iff_count.mpr; intro d
    have occurs : 0<xs.count 2 := List.count_pos_iff.mpr (hi ▸ List.getElem_mem i.isLt)
    have elem : xs[i.val]=2 := hi
    simp only [Y,List.count_cons,List.count_set i.isLt,elem]
    have occ : 2=d → 0<xs.count d := fun e => e ▸ occurs
    simp only [beq_iff_eq]
    by_cases e : 2=d <;> by_cases g : 3=d <;>
      simp (disch := omega) only [ite_eq_left,ite_eq_right] <;> omega
  exact (planaric_perm eqperm).mp init

/-- A degree larger than the number of other core vertices forces an edge
from the root into the suffix of degree-two vertices. -/
theorem exists_two_neighbor {a t : Nat} (rs : List Nat) {G : Graph (a::(rs++List.replicate t 2)).length}
    (hd : G.Realizes (a::(rs++List.replicate t 2))) (high : rs.length<a) :
    ∃ i : Fin (rs++List.replicate t 2).length, rs.length≤i.val ∧ G.adj 0 i.succ=true := by
  let xs := rs++List.replicate t 2
  apply Classical.byContradiction; intro no
  let lift := fun v : Fin rs.length => (⟨v.val+1,by simp [xs]; have := v.isLt; omega⟩ : Fin (a::xs).length)
  let nbr := (List.finRange (a::xs).length).filter (G.adj 0)
  have subset : nbr ⊆ (List.finRange rs.length).map lift := by
    intro v hv
    have he := (List.mem_filter.mp hv).2
    have nz : v≠0 := by rintro rfl; simp at he
    obtain ⟨v,rfl⟩ := Fin.eq_succ_of_ne_zero nz
    have small : v.val<rs.length := by
      apply Nat.lt_of_not_ge; intro large; exact no ⟨v,large,he⟩
    exact List.mem_map.mpr ⟨⟨v.val,small⟩,List.mem_finRange _,rfl⟩
  have bound := List.Nodup.length_le_of_subset ((List.nodup_finRange _).filter _) subset
  have root : nbr.length=a := hd 0
  change nbr.length≤((List.finRange rs.length).map lift).length at bound
  simp only [List.length_map,List.length_finRange] at bound; omega

/-- A hub with more neighbours than there are other core vertices
necessarily sees one of the degree-two vertices in every realization. -/
theorem promote_high_hub {a t : Nat} (rs : List Nat)
    (hp : Planaric (a::(rs++List.replicate t 2))) (high : rs.length<a) :
    Planaric (3::(a+1)::(rs++List.replicate t 2)) := by
  let xs := rs++List.replicate t 2
  obtain ⟨G,hd,hp⟩ := hp
  obtain ⟨i,loc,e⟩ := exists_two_neighbor rs hd high
  apply promote_adjacent_two hp hd i _ e
  change (rs++List.replicate t 2)[i.val]'(i.isLt)=2
  rw [List.getElem_append_right loc]; simp

end SparseBoundary.Fan
