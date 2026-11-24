import SparseBoundary.GraphCliqueSum
import SparseBoundary.GraphRootTwo
import SparseBoundary.PairFromTwo

namespace SparseBoundary.Graph

/-- Replace an edge by two adjacent vertices seeing both former ends.
    Labels zero and one denote the new vertices. -/
def diamond (K : Graph n) (a b : Fin n) : Graph (n+2) :=
  adjoinRow (Fin.cases true (pairRow a b)) (K.subdivide a b)

theorem diamond_planar {K : Graph n} (hp : K.Planar) {a b : Fin n} (edge : K.adj a b=true) :
    (K.diamond a b).Planar := by
  apply clique_sum_edge hp a b edge
  · intro i j
    simp only [diamond,subdivide,adjoin_adj,incident,Fin.cases_succ,erase_adj,eraseRel,Bool.and_eq_true]
    exact And.left
  · intro x
    refine Fin.cases ?_ (fun v => ?_) x
    · intro _ v; simp [diamond,incident,pairRow]
    · refine Fin.cases ?_ (fun y => ?_) v
      · intro _ v; simp only [diamond,subdivide,adjoin_adj,incident,Fin.cases_succ,Fin.cases_zero,
          pairRow,Bool.or_eq_true,beq_iff_eq]; exact id
      · intro hv; simp at hv; omega

theorem diamond_degrees {K : Graph n} {a b : Fin n} (edge : K.adj a b=true) :
    (K.diamond a b).degree 0=3 ∧ (K.diamond a b).degree (0 : Fin (n+1)).succ=3 ∧
      ∀ v : Fin n, (K.diamond a b).degree v.succ.succ=(K.parallelPath a b).degree v.succ := by
  have ne : a≠b := by rintro rfl; simp at edge
  constructor
  · rw [diamond,degree_adjoin_zero,List.finRange_succ]
    simp only [List.filter_cons,Fin.cases_zero,ite_true,List.length_cons,List.filter_map,List.length_map]
    change ((List.finRange n).filter (pairRow a b)).length+1=3
    rw [row_two a b ne]
  constructor
  · rw [diamond,degree_adjoin_succ,subdivide_new_degree edge]; rfl
  · intro v
    rw [diamond,degree_adjoin_succ,subdivide_old_degree edge,parallelPath_old_degree]
    rfl

theorem diamond_edge (K : Graph n) (a b : Fin n) :
    (K.diamond a b).adj 0 (0 : Fin (n+1)).succ=true := by simp only [diamond,adjoin_adj,incident,Fin.cases_zero,Fin.cases_succ]

end SparseBoundary.Graph

namespace SparseBoundary
open Graph

theorem pair_from_triangle {d : List Nat} {g : Nat} {K : Graph d.length} {a b : Fin d.length}
    (hp : K.Planar) (edge : K.adj a b=true) (hg : 3≤g)
    (degrees : ∀ i : Fin d.length, (K.parallelPath a b).degree i.succ=d[i]) :
    Planaric (g::g::(List.replicate (g-3) 2 ++ d)) := by
  let H := K.diamond a b
  let z : Fin (d.length+1) := 0
  let E := List.replicate (g-3) ((0 : Fin (d.length+2)),z.succ)
  have de := diamond_degrees edge
  have pl := expanded_planaric (diamond_planar hp edge) E (by
    intro e he; have he' := List.eq_of_mem_replicate he
    rw [he']; exact diamond_edge ..)
  have row : List.ofFn (fun i => H.degree i + increments E i)=g::g::d := by
    rw [List.ofFn_succ,List.ofFn_succ]
    congr 1
    · have hz : H.degree 0=3 := de.1
      simp [hz,E,increments,List.countP_replicate,pairRow]; omega
    congr 1
    · change H.degree z.succ + increments E z.succ=g
      have hz : H.degree z.succ=3 := de.2.1
      simp [hz,E,increments,List.countP_replicate,pairRow]; omega
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      let v : Fin d.length := ⟨j,hj'⟩
      have dd : H.degree v.succ.succ=d[j] := (de.2.2 v).trans (degrees _)
      have ne : v.succ.succ ≠ z.succ := fun h => Fin.succ_ne_zero v (Fin.succ_inj.mp h)
      simp only [List.getElem_ofFn]
      change H.degree v.succ.succ + increments E v.succ.succ=d[j]
      simp [dd,E,increments,List.countP_replicate,pairRow,ne,Fin.succ_ne_zero]
  change Planaric (List.replicate E.length 2 ++ List.ofFn (fun i => H.degree i + increments E i)) at pl
  rw [row] at pl
  simp only [E,List.length_replicate] at pl
  have perm : (List.replicate (g-3) 2 ++ g::g::d).Perm (g::g::(List.replicate (g-3) 2 ++ d)) :=
    (List.perm_middle (a:=g)).trans ((List.perm_middle (a:=g)).cons g)
  exact (planaric_perm perm).mp pl

/-- Insert two equal high degrees using two designated degree-two entries,
    with no assumption on the rest of the sequence. -/
theorem pair_insertion {d : List Nat} {g : Nat} (hp : Planaric (2::2::d)) (hg : 3≤g) :
    Planaric (g::g::(List.replicate (g-2) 2 ++ d)) := by
  obtain ⟨G,real,plan⟩ := hp
  have deg : G.degree 0=2 := real 0
  let K := G.restrict Fin.succ
  have kp : K.Planar := planar_restrict plan _ (fun i j => Fin.succ_inj.mp)
  obtain ⟨a,b,ne,eqn⟩ := degree_two_root deg
  have eqn' : G=K.parallelPath a b := eqn
  have degrees (i : Fin (2::d).length) : (K.parallelPath a b).degree i.succ=(2::d)[i] := by
    rw [← eqn']; exact real _
  by_cases adjacent : K.adj a b=true
  · have p := pair_from_triangle (g:=g) kp adjacent hg degrees
    have eqr : List.replicate (g-3) 2 ++ (2::d)=List.replicate (g-2) 2 ++ d := by
      have eh : g-2=(g-3)+1 := by omega
      rw [eh]
      have h : List.replicate (g-3) 2 ++ [2]=List.replicate ((g-3)+1) 2 := by
        apply List.eq_replicate_iff.mpr; exact ⟨by simp,by simp; grind⟩
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using congrArg (· ++ d) h
    simpa only [eqr] using p
  · obtain ⟨H,ph,dh⟩ := smooth_root ne (Bool.eq_false_iff.mpr adjacent) (eqn' ▸ plan)
    apply pair_from_two _ hg
    exact ⟨H,fun i => (dh i).trans (degrees i),ph⟩

/-- The equal-pair restoration with the budget in the notation of the two
    boundary theorems. At least two available degree-two vertices suffice. -/
theorem restore_equal_pair {h : List Nat} {s g : Nat} (hs : 2≤s) (hg : 3≤g)
    (hp : Planaric (List.replicate s 2 ++ h)) :
    Planaric (List.replicate (s+g-4) 2 ++ g::g::h) := by
  have es : s=s-2+2 := by omega
  have shape : List.replicate s 2 ++ h=2::2::(List.replicate (s-2) 2 ++ h) := by
    conv => lhs; rw [es,List.replicate_succ,List.replicate_succ]
    rfl
  have hpp := pair_insertion (shape ▸ hp) hg
  have sums : List.replicate (g-2) 2 ++ List.replicate (s-2) 2=List.replicate (s+g-4) 2 := by
    apply List.eq_replicate_iff.mpr; exact ⟨by simp; omega,by simp⟩
  rw [← List.append_assoc,sums] at hpp
  have p : (List.replicate (s+g-4) 2 ++ g::g::h).Perm (g::g::(List.replicate (s+g-4) 2++h)) :=
    (List.perm_middle (a:=g)).trans ((List.perm_middle (a:=g)).cons g)
  exact (planaric_perm p).mpr hpp

end SparseBoundary
