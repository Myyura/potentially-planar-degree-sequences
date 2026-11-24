import SparseBoundary.GraphSupports
import SparseBoundary.GraphEnumeration

namespace Recognition.Examples
open SparseBoundary SparseBoundary.Graph

theorem octahedral : Planaric [4,4,4,4,4,4] :=
  Graph.Octahedron.realize 0 0 0 0 0 0 0 (by decide) (by decide) (by decide) (by decide)

/-- The singleton bags exhibit K_{3,3} in every labelled candidate. -/
theorem three_universal : ¬ Planaric [5,5,5,3,3,3] := by
  let d : List Nat := [5,5,5,3,3,3]
  have test : (candidates 6 (fun i => d[i.val]'i.isLt)).all
      (fun g => g.minorTest biclique33 (fun i => [i])) = true := by decide +kernel
  rintro ⟨g,hd,hp⟩
  exact hp.2 ⟨fun i => [i],List.all_eq_true.mp test g (candidates_complete g _ hd)⟩
end Recognition.Examples
