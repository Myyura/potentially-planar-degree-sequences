import SparseBoundary.GraphDeletion

namespace SparseBoundary.Graph

/-- Join the graph to one new vertex, labelled zero. -/
private def coneRel {n : Nat} (G : Graph n) :
    Fin (n+1) → Fin (n+1) → Bool :=
  Fin.cases (Fin.cases false (fun _ => true)) (fun x => Fin.cases true (G.adj x))

def cone {n : Nat} (G : Graph n) : Graph (n+1) := ofRelation (coneRel G)

@[simp] private theorem cone_adj {n : Nat} (G : Graph n) (v w : Fin (n+1)) :
    G.cone.adj v w = coneRel G v w := by
  apply adj_ofRelation
  · refine Fin.cases ?_ (fun x => ?_)
    · exact Fin.cases rfl (fun _ => rfl)
    · exact Fin.cases rfl (fun y => G.adj_comm x y)
  · exact Fin.cases rfl (fun x => G.adj_self x)

theorem cone_of_universal {n : Nat} (G : Graph (n+1)) (h : G.degree 0 = n) :
    (G.restrict Fin.succ).cone = G := by
  apply eq_of_adj
  refine Fin.cases ?_ (fun x => ?_)
  · refine Fin.cases (by simp) (fun y => ?_)
    simpa [coneRel] using (root_universal h y).symm
  · refine Fin.cases ?_ (fun y => ?_)
    · simpa [coneRel, adj_comm G x.succ 0] using (root_universal h x).symm
    · simp [coneRel]

theorem degree_in_cone {n : Nat} (G : Graph n) (v : Fin n) :
    G.cone.degree v.succ = G.degree v + 1 := by
  simp only [degree, List.finRange_succ, List.filter_cons, cone_adj, coneRel, Fin.cases_succ,
    Fin.cases_zero, ite_true, List.length_cons, List.filter_map, List.length_map]
  rw [show (G.cone.adj v.succ ∘ Fin.succ) = G.adj v from
    funext (fun i => by simp [coneRel])]

set_option maxHeartbeats 1500000 in
/-- A universal first vertex removes one unit of degree from every
    remaining entry. The cone of this unlabelled residual graph is the given
    labelled realization. -/
theorem planaric_universal {n : Nat} (t : List Nat) (hn : t.length = n)
    (h : Planaric (n :: t)) :
    ∃ H : Graph n, H.cone.Planar ∧ ∀ i : Fin n, H.degree i + 1 = t[i.val]'(by omega) := by
  subst n
  obtain ⟨(G : Graph (t.length+1)),hg,hp⟩ := h
  have hg0 : G.degree 0 = t.length := hg 0
  have hc := cone_of_universal (n := t.length) G hg0
  refine ⟨G.restrict (@Fin.succ t.length), ?_, ?_⟩
  · rw [hc]; exact hp
  intro i
  rw [← degree_in_cone, hc]
  exact hg i.succ

end SparseBoundary.Graph
