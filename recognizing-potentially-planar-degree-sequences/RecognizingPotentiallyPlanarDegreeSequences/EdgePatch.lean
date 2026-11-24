import SparseBoundary.GraphCliqueSum
import SparseBoundary.GraphSeries

/-! A pair of common neighbours added at an existing edge, with an optional
edge between the two new vertices. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.EdgePatch
open SparseBoundary SparseBoundary.Graph

/-- Two new common neighbours on an edge. The Boolean selects the edge joining them. -/
def twins (G : Graph n) (u v : Fin n) (join : Bool) : Graph (n+2) :=
  adjoinRow (Fin.cases join (pairRow u v)) (G.parallelPath u v)

theorem twins_planar {G : Graph n} (hp : G.Planar) {u v : Fin n}
    (he : G.adj u v=true) (join : Bool) : (twins G u v join).Planar := by
  apply clique_sum_edge hp u v he
  · simp [twins,parallelPath,incident]
  · intro x hx
    refine Fin.cases ?_ (fun z hz => ?_) x hx
    · simp [twins,incident,pairRow]
    · refine Fin.cases ?_ (fun t ht => ?_) z hz
      · simp only [twins,parallelPath,adjoin_adj,incident,Fin.cases_zero,Fin.cases_succ,pairRow,Bool.or_eq_true,beq_iff_eq]; exact fun _ _ => id
      · change t.val+1+1<2 at ht
        omega

theorem twins_new {G : Graph n} {u v : Fin n} (he : G.adj u v=true) (j : Bool) :
    (twins G u v j).degree 0=2+j.toNat ∧
      (twins G u v j).degree (0 : Fin (n+1)).succ=2+j.toNat := by
  have ne : u≠v := by rintro rfl; simp at he
  constructor
  · rw [twins,degree_adjoin_zero,List.finRange_succ]
    simp only [List.filter_cons,Fin.cases_zero,List.filter_map]
    have hf : (Fin.cases j (pairRow u v) ∘ Fin.succ) = pairRow u v := rfl
    cases j <;> simp [hf,row_two u v ne]
  · rw [twins,degree_adjoin_succ,parallelPath_new_degree he]; rfl

theorem twins_old (G : Graph n) (u v x : Fin n) (j : Bool) :
    (twins G u v j).degree x.succ.succ = G.degree x + 2*(pairRow u v x).toNat := by
  simp [twins,degree_adjoin_succ,parallelPath_old_degree]; omega

end RecognizingPotentiallyPlanarDegreeSequences.EdgePatch
