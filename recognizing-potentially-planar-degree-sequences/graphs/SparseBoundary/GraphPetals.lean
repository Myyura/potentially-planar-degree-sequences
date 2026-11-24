import SparseBoundary.GraphSeries
import SparseBoundary.GraphPerm

namespace SparseBoundary.Graph

/-- Adjoin a triangle sharing exactly its apex with the old graph. -/
def petal (H : Graph n) (v : Fin n) : Graph (n+2) :=
  (H.withLeaf v).parallelPath 0 v.succ

private theorem leaf_at_apex (H : Graph n) (v : Fin n) : (H.withLeaf v).adj 0 v.succ = true := by
  unfold withLeaf
  rw [adj_ofRelation]
  · simp
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
      simp [H.adj_comm]
  · intro i; refine Fin.cases ?_ (fun a => ?_) i <;> simp

theorem petal_planar {H : Graph n} (hp : H.Planar) (v : Fin n) : (H.petal v).Planar :=
  parallelPath_planar (withLeaf_planar hp v) (leaf_at_apex ..)

theorem petal_new (H : Graph n) (v : Fin n) :
    (H.petal v).degree 0=2 ∧ (H.petal v).degree (0 : Fin (n+1)).succ=2 := by
  refine ⟨parallelPath_new_degree (leaf_at_apex ..),?_⟩
  rw [petal,parallelPath_old_degree,withLeaf_new_degree]
  simp [pairRow]

theorem petal_old (H : Graph n) (v i : Fin n) :
    (H.petal v).degree i.succ.succ=H.degree i + if i=v then 2 else 0 := by
  by_cases hh : i=v <;> simp [petal,parallelPath_old_degree,withLeaf_old_degree,pairRow,hh,Fin.succ_ne_zero]

end SparseBoundary.Graph

namespace SparseBoundary

/-- Increase the head degree by two and introduce two degree-two vertices. -/
theorem planaric_petal {a : Nat} {d : List Nat} (hp : Planaric (a::d)) :
    Planaric ((a+2)::(2::2::d)) := by
  obtain ⟨H,real,hp⟩ := hp
  let z : Fin (a::d).length := 0
  have q : Planaric (2::2::(a+2)::d) := by
    refine ⟨H.petal z,?_,Graph.petal_planar hp z⟩
    refine Fin.cases (Graph.petal_new H z).1 (fun i => ?_)
    refine Fin.cases (Graph.petal_new H z).2 (fun j => ?_) i
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [Graph.petal_old]
      simpa [z] using real 0
    · rw [Graph.petal_old]
      simpa [z,Fin.succ_ne_zero] using real k.succ
  exact (planaric_perm (List.perm_middle (a:=a+2) (l₁:=[2,2]) (l₂:=d))).mp q

/-- Iterated petals at a chosen vertex. -/
theorem planaric_petals {a : Nat} {d : List Nat} (hp : Planaric (a::d)) (k : Nat) :
    Planaric ((a+2*k)::(List.replicate (2*k) 2 ++ d)) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    have h := planaric_petal ih
    simpa [Nat.mul_succ,List.replicate_succ,Nat.add_assoc] using h

end SparseBoundary
