import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary
open Graph

/-- Use a degree-two vertex and the subdivision of an incident edge as
    the two equal high vertices. Each further parallel path raises both. -/
theorem pair_from_two {d : List Nat} {g : Nat} (hp : Planaric (2::d)) (hg : 3≤g) :
    Planaric (g::g::(List.replicate (g-2) 2 ++ d)) := by
  obtain ⟨G,real,planar⟩ := hp
  let z : Fin (2::d).length := 0
  have hz : G.degree z=2 := real 0
  have positive : 0<G.degree z := by omega
  obtain ⟨v,hv⟩ := List.length_pos_iff_exists_mem.mp positive
  have adj : G.adj z v=true := (List.mem_filter.mp hv).2
  let H := G.subdivide z v
  have newedge : H.adj 0 z.succ=true := by simp [H,subdivide,incident,pairRow]
  let E := List.replicate (g-2) ((0 : Fin ((2::d).length+1)),z.succ)
  have cert := expanded_planaric (subdivide_planar planar adj) E (by
    intro e he; have eq := List.eq_of_mem_replicate he; rw [eq]; exact newedge)
  have row : List.ofFn (fun i => H.degree i + increments E i) = g::g::d := by
    rw [List.ofFn_succ,List.ofFn_succ]
    congr 1
    · have h0 : H.degree 0=2 := subdivide_new_degree adj
      simp [h0,E,increments,List.countP_replicate,pairRow]; omega
    congr 1
    · have hs : H.degree z.succ=2 := (subdivide_old_degree adj z).trans hz
      change H.degree z.succ + _=g
      change H.degree z.succ + increments E z.succ = g
      simp [hs,E,increments,List.countP_replicate,pairRow]; omega
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      let v : Fin d.length := ⟨j,hj'⟩
      have hh : H.degree v.succ.succ = d[j] := (subdivide_old_degree adj v.succ).trans (real v.succ)
      simp only [List.getElem_ofFn]
      change H.degree v.succ.succ + _ = d[j]
      change H.degree v.succ.succ + increments E v.succ.succ = d[j]
      have ne : v.succ.succ ≠ z.succ := fun he => Fin.succ_ne_zero v (Fin.succ_inj.mp he)
      simp [hh,E,increments,List.countP_replicate,pairRow,ne,Fin.succ_ne_zero]
  change Planaric (List.replicate E.length 2 ++ List.ofFn (fun i => H.degree i + increments E i)) at cert
  rw [row] at cert
  simp only [E,List.length_replicate] at cert
  have p : (List.replicate (g-2) 2 ++ g::g::d).Perm (g::g::(List.replicate (g-2) 2++d)) :=
    (List.perm_middle (a:=g)).trans ((List.perm_middle (a:=g)).cons g)
  exact (planaric_perm p).mp cert

end SparseBoundary
