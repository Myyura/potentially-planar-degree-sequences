import RecognizingPotentiallyPlanarDegreeSequences.Budget
import SparseBoundary.GraphCone
import SparseBoundary.GraphSeries
import SparseBoundary.GraphPerm

/-! Ordinary graphicness of the Euler-tight example lists, independently of
the graph which realizes them after subdivisions. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.Spectrum
open SparseBoundary SparseBoundary.Graph

private theorem empty_graphic (n : Nat) : Graphic (List.replicate n 0) := by
  let d := List.replicate n 0
  let G : Graph d.length := ofRelation (fun _ _ => false)
  have h (i j : Fin d.length) : G.adj i j = false := by apply adj_ofRelation <;> intros <;> rfl
  refine ⟨G,fun i => ?_⟩
  simp [Graph.degree,show G.adj i=(fun _ => false) from funext (h i)]

private theorem graphic_on_labels {d : List Nat} {n : Nat} (hn : d.length = n) :
    Graphic d ↔ ∃ G : Graph n, ∀ i : Fin n, G.degree i = d[i.val]' (by omega) := by
  subst n
  rfl

private theorem cone_graphic {d : List Nat} (dg : Graphic d) :
    Graphic (d.length::d.map (·+1)) := by
  obtain ⟨G,eq⟩ := dg
  apply (graphic_on_labels (n:=d.length+1) (by simp)).mpr
  refine ⟨G.cone,?_⟩
  refine Fin.cases ?_ (fun i => ?_)
  · have h : G.cone.adj 0 ∘ Fin.succ = fun _ => true := by funext i; simp; rfl
    simp only [Graph.degree,List.finRange_succ,List.filter_cons,Graph.adj_self,
      List.filter_map,h]
    simp
  · rw [degree_in_cone,eq]
    simp

/-- The two-apex core is the double cone over a star with one subdivided arm. -/
theorem spectrum_graphic (k m : Nat) :
    Graphic ((k+2*m+3)::(k+2*m+3)::(2*m+3)::(List.replicate k 4 ++ List.replicate (2*m+1) 3)) := by
  let z := 2*m+1
  have seed : Graphic (z::List.replicate z 1) := by simpa using cone_graphic (empty_graphic z)
  have extended : Graphic (List.replicate k 2 ++ z::List.replicate z 1) :=
    Budget.graphic_add_twos seed ⟨z,by simp,by dsimp [z];omega⟩ k
  have tree := (graphic_perm (List.perm_middle (l₁:=List.replicate k 2))).mp extended
  have poles := cone_graphic (cone_graphic tree)
  have ar : 1+(1+(1+2*m))=2*m+3 := by omega
  simpa [z,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,ar] using poles

theorem symmetric_graphic (s : Nat) :
    Graphic ((s+2)::(s+2)::(s+2)::List.replicate s 3) := by
  simpa [Nat.add_assoc] using cone_graphic (cone_graphic (cone_graphic (empty_graphic s)))

end RecognizingPotentiallyPlanarDegreeSequences.Spectrum
