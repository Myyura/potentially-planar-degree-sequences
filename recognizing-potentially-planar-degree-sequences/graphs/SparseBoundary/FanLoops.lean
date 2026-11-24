import SparseBoundary.FanExpansion
import SparseBoundary.LeafLift
import SparseBoundary.GraphPerm

namespace SparseBoundary.Fan

open Graph

private theorem leaf_root (G : Graph n) (v : Fin n) : (G.withLeaf v).adj 0 v.succ=true := by
  unfold withLeaf
  rw [adj_ofRelation]
  · simp
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
      simp [Fin.cases,G.adj_comm]
  · intro i; refine Fin.cases ?_ (fun a => ?_) i <;> simp

/-- A loop at a hub is implemented as a pendant triangle. Both new
vertices have degree two and the old hub gains two. -/
theorem planaric_hub_loop {a : Nat} {us : List Nat} (hp : Planaric (a::us)) :
    Planaric ((a+2)::2::2::us) := by
  obtain ⟨G,hd,hp⟩ := hp
  let L := G.withLeaf 0
  have he : L.adj 0 (Fin.succ 0)=true := leaf_root G _
  let T := copyEdge L 0 (Fin.succ 0)
  have hT : T.Planar := copy_planar (withLeaf_planar hp _) he
  have p : Planaric (2::2::(a+2)::us) := by
    refine ⟨T,?_,hT⟩
    refine Fin.cases (copy_new_degree he) (fun j => ?_)
    refine Fin.cases ?_ (fun i => ?_) j
    · change T.degree (Fin.succ 0)=2
      simp only [T,copy_old_degree,L,withLeaf_new_degree,hit]; simp
    · refine Fin.cases ?_ (fun v => ?_) i
      · change T.degree (Fin.succ (Fin.succ 0))=a+2
        have hg : G.degree 0=a := hd 0
        simp only [T,copy_old_degree,L,withLeaf_old_degree,hg,hit]; simp [Fin.ext_iff]
      · change T.degree v.succ.succ.succ=us[v]
        have hg : G.degree v.succ=us[v] := hd v.succ
        simp only [T,copy_old_degree,L,withLeaf_old_degree,hg,hit]; simp [Fin.ext_iff]
  exact (planaric_perm ((List.Perm.cons 2 (List.Perm.swap (a+2) 2 us)).trans
    (List.Perm.swap (a+2) 2 (2::us)))).mp p

theorem planaric_hub_loops {a : Nat} {us : List Nat} (hp : Planaric (a::us)) (l : Nat) :
    Planaric ((a+2*l)::(List.replicate (2*l) 2 ++ us)) := by
  induction l with
  | zero => simpa using hp
  | succ l ih =>
    have h := planaric_hub_loop ih
    have eqn : 2*(l+1)=2*l+2 := by omega
    simpa only [eqn,List.replicate_succ,List.cons_append,Nat.add_assoc] using h

end SparseBoundary.Fan
