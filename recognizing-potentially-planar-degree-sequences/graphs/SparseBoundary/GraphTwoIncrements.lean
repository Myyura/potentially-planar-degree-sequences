import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary
open Graph

/-- In a labelled realization with its first two vertices adjacent, adding
    a parallel two-edge path raises exactly those two entries by one. -/
theorem first_two_increments {a b : Nat} {d : List Nat} {G : Graph (a::b::d).length}
    (real : G.Realizes (a::b::d)) (hp : G.Planar) (edge : G.adj 0 (0 : Fin (b::d).length).succ=true) :
    Planaric (2::(a+1)::(b+1)::d) := by
  let v : Fin (a::b::d).length := (0 : Fin (b::d).length).succ
  refine ⟨G.parallelPath 0 v,?_,parallelPath_planar hp edge⟩
  refine Fin.cases (parallelPath_new_degree edge) (fun u => ?_)
  refine Fin.cases ?_ (fun j => ?_) u
  · rw [parallelPath_old_degree,real]; simp [pairRow]
  · refine Fin.cases ?_ (fun k => ?_) j
    · rw [parallelPath_old_degree,real]; change b+(pairRow 0 v v).toNat=b+1; simp [pairRow]
    · rw [parallelPath_old_degree,real]
      have ne : k.succ.succ≠v := fun h => Fin.succ_ne_zero k (Fin.succ_inj.mp h)
      simp [pairRow,ne,Fin.succ_ne_zero]

end SparseBoundary
